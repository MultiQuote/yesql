(ns yesql.generate
  (:require [clojure.java.jdbc :as jdbc]
            [clojure.set :as set]
            [clojure.string :refer [join lower-case]]
            [yesql.util :refer [create-root-var]]
            [yesql.types :refer [map->Query]]
            [yesql.statement-parser :refer [tokenize]]
            [clojure.core.async :as async])
  (:import [yesql.types Query]))

(def in-list-parameter?
  "Check if a type triggers IN-list expansion."
  (some-fn list? vector? seq?))

(defn- args-to-placeholders
  [args]
  (if (in-list-parameter? args)
    (clojure.string/join "," (repeat (count args) "?"))
    "?"))

(defn- analyse-statement-tokens
  [tokens]
  {:expected-keys (set (map keyword (remove (partial = '?)
                                            (filter symbol? tokens))))
   :expected-positional-count (count (filter (partial = '?)
                                             tokens))})

(defn expected-parameter-list
  [query]
  (let [tokens (tokenize query)
        {:keys [expected-keys expected-positional-count]} (analyse-statement-tokens tokens)]
    (if (zero? expected-positional-count)
      expected-keys
      (conj expected-keys :?))))

(defn rewrite-query-for-jdbc
  [tokens initial-args]
  (let [{:keys [expected-keys expected-positional-count]} (analyse-statement-tokens tokens)
        actual-keys (set (keys (dissoc (if (sequential? initial-args) (apply merge initial-args) initial-args) :?)))
        actual-positional-count (count (:? initial-args))
        missing-keys (set/difference expected-keys actual-keys)]
    (if-not (empty? missing-keys)
      (throw (IllegalArgumentException. (format "Query argument mismatch.\nExpected keys: %s\nActual keys: %s\nMissing keys: %s"
                                                (str (seq expected-keys))
                                                (str (seq actual-keys))
                                                (str (seq missing-keys))))))
    (if-not (= expected-positional-count actual-positional-count)
      (throw (IllegalArgumentException. (format (join "\n"
                                                      ["Query argument mismatch."
                                                       "Expected %d positional parameters. Got %d."
                                                       "Supply positional parameters as {:? [...]}"])
                                                expected-positional-count actual-positional-count))))
    (if (sequential? initial-args)
      (let [[final-query final-parameters consumed-args]
            (reduce (fn [[query parameters args] token]
                      (cond
                        (string? token) [(str query token)
                                         parameters
                                         args]
                        (symbol? token) [(str query (args-to-placeholders ""))
                                         (conj parameters (keyword token))
                                         args])) ["" [] initial-args] tokens)] (concat [final-query] (mapv (apply juxt final-parameters) initial-args)))
      (let [[final-query final-parameters consumed-args]
            (reduce (fn [[query parameters args] token]
                      (cond
                        (string? token) [(str query token)
                                         parameters
                                         args]
                        (symbol? token) (let [[arg new-args] (if (= '? token)
                                                               [(first (:? args)) (update-in args [:?] rest)]
                                                               [(get args (keyword token)) args])]
                                          [(str query (args-to-placeholders arg))
                                           (vec (if (in-list-parameter? arg)
                                                  (concat parameters arg)
                                                  (conj parameters arg)))
                                           new-args])))
                    ["" [] initial-args]
                    tokens)]
        (concat [final-query] final-parameters)))))


;; Maintainer's note: clojure.java.jdbc.execute! returns a list of
;; rowcounts, because it takes a list of parameter groups. In our
;; case, we only ever use one group, so we'll unpack the
;; single-element list with `first`.
(defn execute-handler
  [db sql-and-params call-options]
  (first (jdbc/execute! db sql-and-params)))

(defn insert-handler
  [db statement-and-params call-options]
  (if (sequential? (second statement-and-params))
    (jdbc/db-do-prepared db true statement-and-params {:multi? true})
    (jdbc/db-do-prepared-return-keys db statement-and-params)))

(defn query-handler
  [db sql-and-params {:keys [row-fn result-set-fn identifiers as-arrays?]
                      :or   {identifiers   identity
                             row-fn        identity
                             result-set-fn doall}
                      :as   call-options}]
  (jdbc/query db sql-and-params {:as-arrays?    as-arrays?
                                 :identifiers   identifiers
                                 :row-fn        row-fn
                                 :result-set-fn result-set-fn}))

(defn query-handler-stream
  [db sql-and-params {:keys [row-fn identifiers as-arrays? result-channel fetch-size]
                      :or   {identifiers identity
                             row-fn      identity
                             fetch-size  1}}]
  (let [call-options {:as-arrays?  as-arrays?
                      :identifiers identifiers
                      :row-fn      row-fn
                      :fetch-size  fetch-size}]
    (assert result-channel "You must supply a result channel e.g. {:result-channel `chan`}")
    (jdbc/db-query-with-resultset
      db
      sql-and-params
      (fn [rs]
        (loop [[row & rows] (jdbc/result-set-seq rs call-options)]
          (if-not row
            (do
              (async/>!! result-channel :result-set-end)
              (async/close! result-channel))
            (when (async/>!! result-channel row)
              (recur rows)))))
      call-options)))

(defn generate-query-fn
  "Generate a function to run a query.

  - If the query name ends in `!` it will call `clojure.java.jdbc/execute!`,
  - If the query name ends in `<!` it will call `clojure.java.jdbc/insert!`,
  - otherwise `clojure.java.jdbc/query` will be used."
  [{:keys [name docstring statement]
    :as query}
   query-options]
  (assert name      "Query name is mandatory.")
  (assert statement "Query statement is mandatory.")
  (let [jdbc-fn (cond
                  (= (take-last 2 name) [\< \!]) insert-handler
                  (= (last name) \!) execute-handler
                  (:stream? query-options) query-handler-stream
                  :else query-handler)
        required-args (expected-parameter-list statement)
        global-connection (:connection query-options)
        tokens (tokenize statement)
        real-fn (fn [args call-options]
                  (let [connection (or (:connection call-options)
                                       global-connection)]
                    (assert connection
                            (format (join "\n"
                                          ["No database connection supplied to function '%s',"
                                           "Check the docs, and supply {:connection ...} as an option to the function call, or globally to the defquery declaration."])
                                    name))
                    (jdbc-fn connection
                             (rewrite-query-for-jdbc tokens args)
                             call-options)))
        [display-args generated-function] (let [named-args (if-let [as-vec (seq (mapv (comp symbol clojure.core/name)
                                                                                      required-args))]
                                                             {:keys as-vec}
                                                             {})
                                                global-args {:keys ['connection]}]
                                            (if global-connection
                                              (if (empty? required-args)
                                                [(list []
                                                       [named-args global-args])
                                                 (fn query-wrapper-fn
                                                   ([] (query-wrapper-fn {} {}))
                                                   ([args call-options] (real-fn args call-options)))]
                                                [(list [named-args]
                                                       [named-args global-args])
                                                 (fn query-wrapper-fn
                                                   ([args] (query-wrapper-fn args {}))
                                                   ([args call-options] (real-fn args call-options)))])
                                              [(list [named-args global-args])
                                               (fn query-wrapper-fn
                                                 ([args call-options] (real-fn args call-options)))]))]
    (with-meta generated-function
      (merge {:name name
              :arglists display-args
              ::source (str statement)}
             (when docstring
               {:doc docstring})))))

(defn generate-var [this options]
  (create-root-var (:name this)
                   (generate-query-fn this options)))
