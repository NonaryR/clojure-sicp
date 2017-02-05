(ns clojure-sicp.chapter4
  (:refer-clojure :exclude (==))
  (:require [clojure.math.combinatorics :as combo]
            [clojure.core.logic.fd :as fd])
  (:use [clojure.core.logic]
        [clojure.core.logic.pldb :rename {db-rel defrel}]))

(declare primes)

(defn prime?
  [n]
  (let [limit (Math/sqrt (inc n))]
    (every? #(not= (rem n %) 0)
            (take-while #(< % limit) primes))))

(def primes
  (lazy-cat [2 3]
            (filter prime? (iterate inc 5))))

(defn eval-seq
  [eval]
  (fn [coll env]
    (if (empty? coll)
      nil
      (loop [exps coll]
        (if (empty? (rest exps))
          (eval (first exps) env)
          (do
            (eval (first exps) env)
            (recur (rest exps))))))))

(defprotocol Environmental
  (env-extend  [this bindings])
  (env-lookup  [this var])
  (env-set!    [this var value])
  (env-define! [this var value]))

(deftype Env [bindings enclose])

(def base-env-behavior
  {:env-extend (fn [this bindings]
                 (Env. (atom bindings) this))
   :env-lookup (fn [this var]
                 (loop [env this]
                   (let [bindings @(.bindings env)
                         enclose   (.enclose  env)]
                     (if (contains? bindings var)
                       (get bindings var)
                       (if-not enclose
                         (throw (Exception.
                                 (print-str "Unbound variable:" var)))
                         (recur enclose))))))
   :env-set! (fn [this var value]
               (loop [env this]
                 (let [bindings (.bindings env)
                       enclose  (.enclose  env)]
                   (if (contains? @bindings var)
                     (do
                       (swap! bindings assoc var value)
                       var)
                     (if-not enclose
                       (throw (Exception.
                               (print-str "Unbound variable:" var)))
                       (recur enclose))))))
   :env-define! (fn [this var value]
                  (swap! (.bindings this) assoc var value)
                  var)})

(extend Env
  Environmental
  base-env-behavior)

(defn make-env
  ([bindings]
     (make-env bindings nil))
  ([bindings enclose]
     (Env. (atom bindings) enclose)))

(defprotocol Appliable
  (my-apply [this args env eval]))

(deftype Procedure [params body env]
  Appliable
  (my-apply [this args env eval]
    (let [env (env-extend (.env this)
                          (zipmap (.params this) args))]
      ((eval-seq eval) (.body this) env))))

(deftype Primitive [fn]
  Appliable
  (my-apply [this args env eval]
    (apply (.fn this) args)))

(defn applicative-apply
  [exp env eval]
  (let [[proc & args] (map #(eval % env) exp)]
    (my-apply proc args env eval)))

(defn self-eval?
  [exp]
  (or (number? exp)
      (string? exp)
      (true? exp)
      (false? exp)
      (nil? exp)
      (= exp '())))

(defn variable?
  [exp]
  (symbol? exp))

(defn make-eval
  [special-forms apply-fn]
  (fn ! [exp env]
    (cond (self-eval? exp) exp
          (variable? exp)  (env-lookup env exp)
          ;; special forms
          :else
          (let [[op & rest] exp
                op (keyword op)]
            (if (contains? special-forms op)
              ;; special forms
              ((get special-forms op) rest env !)
              ;; application
              (apply-fn exp env !))))))

(def ^:dynamic ^:private *gensyms*)

(defn resolve
  [sym]
  (let [ns (namespace sym)
        n (name sym)]
    (if (and (not ns) (= (last n) \#))
      (if-let [gs (@*gensyms* sym)]
        gs
        (let [gs (gensym (str (subs n 0 (dec (count n))) "__auto__"))]
          (swap! *gensyms* assoc sym gs)
          gs))
      sym)))

(defn unquote?
  [form]
  (and (seq? form) (= (first form) 'clojure.core/unquote)))

(defn unquote-splicing?
  [form]
  (and (seq? form) (= (first form) 'clojure.core/unquote-splicing)))

(defn record?
  [x]
  (instance? clojure.lang.IRecord x))

(defn quasiquote-fn*
  [form]
  (cond
   (symbol? form) `'~(resolve form)
   (unquote? form) (second form)
   (unquote-splicing? form) (throw (Exception. "splice not in list"))
   (record? form) `'~form
   (coll? form)
   (let [xs (if (map? form) (apply concat form) form)
         parts (for [x (partition-by unquote-splicing? xs)]
                 (if (unquote-splicing? (first x))
                   (second (first x))
                   (mapv quasiquote-fn* x)))
         cat (doall `(concat ~@parts))]
     (cond
      (vector? form) `(vec ~cat)
      (map? form) `(apply hash-map ~cat)
      (set? form) `(set ~cat)
      (seq? form) `(apply list ~cat)
      :else (throw (Exception. "Unknown collection type"))))
   :else `'~form))

(defn quasiquote-fn
  [form]
  (binding [*gensyms* (atom {})]
    (quasiquote-fn* form)))

(defmacro quasiquote
  [form]
  (quasiquote-fn form))

(defn eval-quote [[x] _ _] x)

(defn eval-assign
  [[v o] env eval]
  (env-set! env v (eval o env))
  'ok)

(defn desugar-define
  [[name & params] & body]
  (quasiquote (define ~name (lambda ~params ~@body))))

(defn eval-define
  [exp env eval]
  (if (symbol? (first exp))
    (let [[v o] exp]
      (env-define! env v (eval o env)))
    (eval (apply desugar-define exp) env))
  'ok)

(defn eval-if
  [[pred conseq alt] env eval]
  (if (eval pred env)
    (eval conseq env)
    (eval alt    env)))

(defn eval-lambda
  [[params & body] env _]
  (Procedure. params body env))

(defn eval-begin
  [exp env eval]
  ((eval-seq eval) exp env))

(defn seq->exp
  ([] nil)
  ([coll]
     (cond (empty? coll) coll
           (empty? (rest coll)) (first coll)
           :else (quasiquote (begin ~@coll)))))

(defn cond->if
  ([] false)
  ([[[pred & act] & next :as clauses]]
     (if (= pred 'else)
       (if (empty? next)
         (seq->exp act)
         (throw (Exception.
                 (print-str "ELSE clause isn't last:" clauses))))
       (list 'if pred (seq->exp act) (cond->if next)))))

(defn eval-cond
  [exp env eval]
  (eval (cond->if exp) env))

(def pristine-primitives-map
  {'car    first
   'cdr    rest
   'cons   cons
   'null?  empty?
   'not    not
   'list   list
   'even?  even?
   'odd?   odd?
   'prime? prime?
   '+      +
   '-      -
   '*      *
   '/      /
   '=      =
   '<      <
   '>      >
   '<=     <=
   '>=     >=} )

(def pristine-primitives
  (let [m pristine-primitives-map]
    (into {} (for [[k v] m] [k (Primitive. v)]))))

(def pristine-special-forms
  {:quote   eval-quote
   :set!    eval-assign
   :define  eval-define
   :if      eval-if
   :lambda  eval-lambda
   :begin   eval-begin
   :cond    eval-cond})

(def pristine-eval
  (make-eval pristine-special-forms applicative-apply))

;;; Exercise 4.1

(defn list-of-values-ltr [exps]
  (if (empty? exps)
    '()
    (#(cons % (list-of-values-ltr (rest exps)))
     (eval (first exps)))))

;;; Exercice 4.2 (b)

(defn tagged-list?
  [exp tag]
  (if (list? exp)
    (= tag (first exp))
    false))

(defn louis-application?
  [exp]
  (tagged-list? exp 'call))

(defn louis-operator
  [exp]
  (second exp))

(defn louis-operands
  [exp]
  (drop 2 exp))

;;; Exercise 4.3

(defn car
  [x] (first x))

(defn cdr
  [x]
  (next x))

(defn cadr
  [x]
  (second x))

(defn caddr
  [x]
  (first (next (next x))))

(defn cdddr
  [x]
  (next (next (next x))))

(defn caddr
  [x]
  (first (next (next x))))

(defn cadddr
  [x]
  (first (next (next (next x)))))

(defn null?
  [x]
  (nil? x))

(defn enclosing-environment
  [env]
  (rest env))

(defn first-frame
  [env]
  (car env))

(def the-empty-environment '())

(defn make-frame
  [variables values]
  (atom (zipmap variables values)))

(defn frame-variables
  [frame]
  (keys @frame))

(defn frame-values
  [frame]
  (vals @frame))

(defn add-binding-to-frame!
  [var val frame]
  (swap! frame assoc var val))

(defn extend-environment
  [vars vals base-env]
  (if (= (count vars) (count vals))
    (cons (make-frame vars vals) base-env)
    (if (< (count vars) (count vals))
      (Error. (str "Too many arguments supplied " vars vals))
      (Error. (str "Too few arguments supplied " vars vals)))))

(defn copy-environment
  [e]
  (doall (map #(atom @%) e)))

(defn environments-equal?
  [x y]
  (reduce #(and %1 %2) true (map #(= @%1 @%2) x y)))

(defn lookup-variable-value
  [variable env]
  (letfn [(env-loop [env]
            (letfn [(scan [frame]
                      (if (contains? frame variable)
                        (let [value (get frame variable)]
                          (if (= value '*unassigned*)
                            (Error. (str "Unassigned variable " variable))
                            value))
                        (env-loop (enclosing-environment env))))]
              (if (= env the-empty-environment)
                (Error. (str "Unbound variable " variable))
                (let [frame (first-frame env)]
                  (scan @frame)))))]
    (env-loop env)))


(defn set-variable-value!
  [variable value env]
  (letfn [(env-loop [env]
            (letfn [(scan [frame]
                      (if (contains? @frame variable)
                        (swap! frame assoc variable value)
                        (env-loop (enclosing-environment env))))]
              (if (= env the-empty-environment)
                (Error. (str "Unbound variable -- SET! " variable))
                (scan (first-frame env)))))]
    (env-loop env)))

(defn define-variable!
  [variable value env]
  (swap! (first-frame env) assoc variable value))

(defn unbind-variable!
  [variable env]
  (swap! (first-frame env) dissoc variable))


(declare execute-application
         primitive-procedure-names
         primitive-procedure-objects
         expand-clauses)

(declare my-eval
         my-apply
         analyze)

(declare no-operands?
         first-operand
         rest-operands)

(defn list-of-values
  [exps env]
  (if (no-operands? exps)
    '()
    (let [left (my-eval (first-operand exps) env)
          right (list-of-values (rest-operands exps) env)]
      (cons left right))))

(declare if-predicate if-alternative if-consequent)

(defn tag
  [exp]
  (if (seq? exp)
    (first exp)
    (Error. (str "this shouldn't happen"))))

(defn eval-if
  [exp env]
  (if (true? (my-eval (if-predicate exp) env))
      (my-eval (if-consequent exp) env)
      (my-eval (if-alternative exp) env)))

(declare last-exp? first-exp rest-exps)

(defn eval-sequence
  [exps env]
  (cond (last-exp? exps) (my-eval (first-exp exps) env)
        :else (do (my-eval (first-exp exps) env)
                  (eval-sequence (rest-exps exps) env))))

(declare assignment-variable assignment-value)

(defn eval-assignment
  [exp env]
  (set-variable-value! (assignment-variable exp)
                       (my-eval (assignment-value exp) env)
                       env)
  'ok)

(declare definition-variable definition-value)

(defn eval-definition
  [exp env]
  (define-variable!
    (definition-variable exp)
    (my-eval (definition-value exp) env)
    env)
  'ok)

(defn self-evaluating?
  [exp]
  (cond (number? exp) true
        (string? exp) true
        :else false))

(defn variable? [exp]
  (or (symbol? exp)
      (= 'true exp)
      (= 'false exp)))

(defn tagged-list?
  [exp tag]
  (if (seq? exp)
    (= (first exp) tag)
    false))

(defn text-of-quotation
  [exp]
  (cadr exp))

(defn assignment-variable
  [exp]
  (second exp))

(defn assignment-value
  [exp]
  (nth exp 2))

(defn definition-variable
  [exp]
  (if (symbol? (second exp))
    (second exp)
    (first (first (rest exp)))))

(declare make-lambda)

(defn definition-value
  [exp]
  (if (symbol? (second exp))
    (nth exp 2)
    (make-lambda (rest (first (rest exp)))
                 (rest (rest exp)))))

(defn lambda-parameters
  [exp]
  (second exp))

(defn lambda-body
  [exp]
  (rest (rest exp)))

(defn make-lambda
  [parameters body]
  (cons 'lambda (cons parameters body)))

(defn if-predicate
  [exp]
  (cadr exp))

(defn if-consequent
  [exp]
  (caddr exp))

(defn if-alternative
  [exp]
  (if (not (nil? (cdddr exp)))
    (cadddr exp)
    'false))

(defn make-if
  [predicate consequent alternative]
  (list 'if predicate consequent alternative))

(defn begin-actions
  [exp]
  (cdr exp))

(defn last-exp?
  [xs]
  (null? (cdr xs)))

(defn first-exp
  [xs]
  (car xs))

(defn rest-exps
  [xs]
  (cdr xs))

(defn make-begin
  [xs]
  (cons 'begin xs))

(defn sequence->exp
  [xs]
  (cond (null? xs) xs
        (last-exp? xs) (first-exp xs)
        :else (make-begin xs)))

(defn pair?
  [x]
  (seq? x))

(defn application?
  [exp]
  (pair? exp))

(defn operator
  [exp]
  (car exp))

(defn operands
  [exp]
  (cdr exp))

(defn no-operands?
  [ops]
  (null? ops))

(defn first-operand
  [ops]
  (car ops))

(defn rest-operands
  [ops]
  (cdr ops))

(defn cond-clauses
  [exp]
  (cdr exp))

(defn cond-predicate
  [clause]
  (car clause))

(defn cond-else-clause?
  [clause]
  (= (cond-predicate clause) 'else))

(defn cond-actions
  [clause]
  (cdr clause))

(defn cond->if
  [exp]
  (expand-clauses (cond-clauses exp)))

(defn expand-clauses
  [clauses]
  (if (null? clauses)
    'false
    (let [first-clause (car clauses)
          rest-clauses (cdr clauses)]
      (if (cond-else-clause? first-clause)
        (if (null? rest-clauses)
          (sequence->exp (cond-actions first-clause))
          (Error. (str  "ELSE clause isn't last -- COND->IF"
                        clauses)))
        (make-if (cond-predicate first-clause)
                 (sequence->exp (cond-actions first-clause))
                 (expand-clauses rest-clauses))))))

(defn make-procedure
  [parameters body env]
  (list 'procedure parameters body env))

(defn compound-procedure?
  [p]
  (tagged-list? p 'procedure))

(defn procedure-parameters
  [p]
  (cadr p))

(defn procedure-body
  [p]
  (caddr p))

(defn procedure-environment
  [p]
  (cadddr p))

(defn analyze-sequence
  [exps]
  (letfn [(sequentially [proc1 proc2]
                        (fn [env] (proc1 env) (proc2 env)))
          (lop [first-proc rest-procs]
               (if (null? rest-procs)
                 first-proc
                 (lop (sequentially first-proc (car rest-procs))
                      (cdr rest-procs))))]
    (let [procs (map analyze exps)]
      (if (null? procs)
        (Error. "Empty sequence -- ANALYZE"))
      (lop (car procs) (cdr procs)))))

(defn analyze-application
  [exp]
  (let [fproc (analyze (operator exp))
        aprocs (map analyze (operands exp))]
    (fn [env]
      (execute-application (fproc env)
                           (map (fn [aproc] (aproc env))
                                aprocs)))))

(defn analyze-self-evaluating
  [exp]
  (fn [env] exp))

(defn analyze-quoted
  [exp]
  (let [qval (text-of-quotation exp)]
    (fn [env] qval)))

(defn analyze-variable
  [exp]
  (fn [env] (lookup-variable-value exp env)))

(defn analyze-assignment
  [exp]
  (let [var (assignment-variable exp)
        vproc (analyze (assignment-value exp))]
    (fn [env]
      (set-variable-value! var (vproc env) env)
      'ok)))

(defn analyze-definition
  [exp]
  (let [var (definition-variable exp)
        vproc (analyze (definition-value exp))]
    (fn [env]
      (define-variable! var (vproc env) env)
      'ok)))

(defn analyze-if
  [exp]
  (let [pproc (analyze (if-predicate exp))
        cproc (analyze (if-consequent exp))
        aproc (analyze (if-alternative exp))]
    (fn [env]
      (if (true? (pproc env))
        (cproc env)
        (aproc env)))))

(defn analyze-lambda
  [exp]
  (let [vars (lambda-parameters exp)
        bproc (analyze-sequence (lambda-body exp))]
    (fn [env] (make-procedure vars bproc env))))

(def primitive-procedures
     (list (list 'car car)
           (list 'cdr cdr)
           (list 'cons cons)
           (list 'null? null?)
           (list '+ +)
           (list '- -)
           (list '* *)
           (list '/ /)
           (list '= =)
           (list '> >)
           (list '< <)
           (list 'and (fn [& xs] (reduce #(and %1 %2) true xs)))
           (list 'or (fn [& xs] (reduce #(or %1 %2) false xs)))))

(defn primitive-procedure-names
  []
  (map car primitive-procedures))

(defn primitive-procedure-objects
  []
  (map (fn [proc] (list 'primitive (cadr proc)))
       primitive-procedures))

(defn setup-environment
  []
  (let [initial-env
        (extend-environment (primitive-procedure-names)
                            (primitive-procedure-objects)
                            the-empty-environment)]
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    initial-env))

(def the-global-environment (setup-environment))

(defn reset-global-environment
  []
  (def the-global-environment (setup-environment)))

(defn primitive-procedure?
  [proc]
  (tagged-list? proc 'primitive))

(defn primitive-implementation
  [proc]
  (cadr proc))

(defn apply-primitive-procedure
  [proc args]
  (apply (primitive-implementation proc) args))

(defn execute-application
  [proc args]
  (cond (primitive-procedure? proc)
          (apply-primitive-procedure proc args)
        (compound-procedure? proc)
          ((procedure-body proc)
           (extend-environment (procedure-parameters proc)
                               args
                               (procedure-environment proc)))
        :else
        (Error. (str
                 "Unknown procedure type -- EXECUTE-APPLICATION"
                 proc))))

(defmulti analyze-method tag)
(defmethod analyze-method 'quoted [exp] (analyze-quoted exp))
(defmethod analyze-method 'assignment [exp] (analyze-assignment exp))
(defmethod analyze-method 'definition  [exp] (analyze-definition exp))
(defmethod analyze-method 'if [exp] (analyze-if exp))
(defmethod analyze-method 'labmda [exp] (analyze-lambda exp))
(defmethod analyze-method 'begin [exp] (analyze-sequence (begin-actions exp)))
(defmethod analyze-method 'cond [exp] (analyze (cond->if exp)))
(defmethod analyze-method :default [exp] (analyze-application exp))

(defmulti eval-method
  (fn [exp env] (tag exp)))


; This method applys the function.
(defmethod eval-method :default [exp env]
  (my-apply (my-eval (operator exp) env)
            (list-of-values (operands exp) env)))

(defmethod eval-method 'quote
  [exp env]
  (text-of-quotation exp))

(defmethod eval-method 'set!
  [exp env]
  (eval-assignment exp env))

(defmethod eval-method 'define
  [exp env]
  (eval-definition exp env))

(defmethod eval-method 'lambda
  [exp env]
  (make-procedure (lambda-parameters exp)
                  (lambda-body exp)
                  env))

(defmethod eval-method 'if
  [exp env]
  (eval-if exp env))

(defmethod eval-method 'begin
  [exp env]
  (eval-sequence (begin-actions exp) env))

(defmethod eval-method 'cond
  [exp env]
  (my-eval (cond->if exp) env))

(defn analyze
  [exp]
  (cond (self-evaluating? exp)
        (analyze-self-evaluating exp)
        (variable? exp) (analyze-variable exp)
        :else (analyze-method exp)))

(defn my-eval
  [exp env]
  (cond (self-evaluating? exp) exp
        (variable? exp) (lookup-variable-value exp env)
        :else (eval-method exp env)))

(defn my-apply
  [procedure arguments]
  (cond (primitive-procedure? procedure)
          (apply-primitive-procedure procedure arguments)
        (compound-procedure? procedure)
          (eval-sequence
           (procedure-body procedure)
           (extend-environment
            (procedure-parameters procedure)
            arguments
            (procedure-environment procedure)))
        :else (Error. (str "Unknown procedure type -- APPLY " procedure))))

(defn interpret
  [exp]
  (my-eval exp the-global-environment))

;;; Exercise 4.4

(defn and->if
  ([] true)
  ([x] x)
  ([x & next]
     (list 'if x (apply and->if next) x)))

(defn eval-and
  [exp env eval]
  (eval (apply and->if exp) env))

(defn or->if
  ([] nil)
  ([x] x)
  ([x & next]
     (list 'if x x (apply or->if next))))

(defn eval-or
  [exp env eval]
  (eval (apply or->if exp) env))

(def special-forms-with-and-or
  (assoc pristine-special-forms :and eval-and :or eval-or))

(def eval-with-and-or
  (make-eval special-forms-with-and-or applicative-apply))

;;; Exercise 4.6

(defn let->combination
  [bindings & body]
  (let [names  (map first bindings)
        values (map second bindings)]
    (quasiquote ((lambda ~names ~@body) ~@values))))

(defn eval-let
  [exp env eval]
  (eval (apply let->combination exp) env))

(def special-forms-with-let
  (assoc pristine-special-forms :let eval-let))

(def eval-with-let
  (make-eval special-forms-with-let applicative-apply))

;;; Exercise 4.7

(defn let*->nested-lets
  [bindings & body]
  (letfn [(iter [names values]
            (if (or (empty? (rest names))
                    (empty? (rest values)))
              (quasiquote (let ((~(first names) ~(first values))) ~@body))
              (quasiquote (let ((~(first names) ~(first values)))
                            ~(iter (rest names) (rest values))))))]
    (iter (map first bindings) (map second bindings))))

(defn eval-let*
  [exp env eval]
  (eval (apply let*->nested-lets exp) env))

(def special-forms-with-let*
  (assoc special-forms-with-let :let* eval-let*))

(def eval-with-let*
  (make-eval special-forms-with-let* applicative-apply))

;;; Exercise 4.8

(defn named-let->combination
  [& args]
  (if (symbol? (first args))
    (let [[name bindings & body] args]
      (quasiquote (((lambda ()
                            (define (~name ~@(map first bindings)) ~@body)
                            ~name))
                   ~@(map second bindings))))
    (apply let->combination args)))

(defn eval-named-let
  [exp env eval]
  (eval (apply named-let->combination exp) env))

(def special-forms-with-named-let
  (assoc pristine-special-forms :let eval-named-let))

(def eval-with-named-let
  (make-eval special-forms-with-named-let applicative-apply))

;;; Exercise 4.13

(defn unbind?
  [exp]
  (tagged-list? exp 'make-unbound!))

(defn eval-unbind
  [exp env]
  (unbind-variable! (second exp) env)
  'ok)

(defn primitive-procedure?
  [proc]
  (tagged-list? proc 'primitive))

(defn primitive-implementation
  [proc]
  (cadr proc))

(defn apply-primitive-procedure
  [proc args]
  (apply (primitive-implementation proc) args))

(defn execute-application
  [proc args]
  (cond (primitive-procedure? proc)
          (apply-primitive-procedure proc args)
        (compound-procedure? proc)
          ((procedure-body proc)
           (extend-environment (procedure-parameters proc)
                               args
                               (procedure-environment proc)))
        :else
        (Error. (str
                 "Unknown procedure type -- EXECUTE-APPLICATION"
                 proc))))

(defn is-define?
  [e]
  (and (seq? e)
       (tagged-list? e 'define)))

(defn find-defines
  [exp]
  (filter is-define? exp))

(defn defined-variables
  [defs]
  (map second defs))

(defn defined-values
  [defs]
  (map #(nth % 2) defs))

(defn non-defines
  [exp]
  (remove is-define? exp))

;;; Exercise 4.16

(def env-with-unassigned-behavior
  (merge base-env-behavior
         {:env-lookup
          (fn [this var]
            (loop [env this]
              (let [bindings @(.bindings env)
                    enclose   (.enclose  env)]
                (if (contains? bindings var)
                  (let [val (get bindings var)]
                    (if (= val '*unassigned*)
                      (throw (Exception.
                              (print-str "Unassigned variable:" var)))
                      val))
                  (if-not enclose
                    (throw (Exception.
                            (print-str "Unbound variable:" var)))
                    (recur enclose))))))}))

(deftype UnassignableEnv [bindings enclose])
(extend UnassignableEnv
  Environmental
  env-with-unassigned-behavior)

(defn make-unassignable-env
  ([bindings]
     (make-unassignable-env bindings nil))
  ([bindings enclose]
     (UnassignableEnv. (atom bindings) enclose)))

;;; Exercise 4.19

(defn letrec->let
  [bindings & body]
  (let [names  (map first  bindings)
        values (map second bindings)]
    (quasiquote (let ~(map #(list % ''*unassigned*) names)
                  ~@((fn ! [bindings]
                       (if (empty? bindings)
                         body
                         (let [[[k v] & next] bindings]
                           (quasiquote ((set! ~k ~v) ~@(! next))))))
                     bindings)))))

(defn eval-letrec
  [exp env eval]
  (eval (apply letrec->let exp) env))

(def special-forms-with-letrec
  (assoc special-forms-with-let :letrec eval-letrec))

(def eval-with-leterec
  (make-eval special-forms-with-letrec applicative-apply))

;;; Exercise 4.21

(defn recursive-even?
  [x]
  ((fn [even? odd?]
     (even? even? odd? x))
   (fn [ev? od? n]
     (if (zero? n) true (od? ev? od? (dec n))))
   (fn [ev? od? n]
     (if (zero? n) false (ev? ev? od? (dec n))))))

;;; Exercise 4.20

(defn make-let
  [clauses body]
  (list 'let clauses body))

(defn letrec?
  [exp]
  (tagged-list? exp 'letrec))

(defn letrec->let
  [exp]
  (let [fns (second exp)
        fn-names (map first fns)
        fn-vals  (map second fns)
        body (nth exp 2)]
    (make-let
     (map #(list % ''*unassigned*) fn-names)
     (make-begin
      (concat
       (map #(list 'set! %1 %2) fn-names fn-vals)
       (list body))))))

;;; Exercise 4.21

(defn factorial [n]
  ((fn [fact]
     (fact fact n))
   (fn [ft k]
     (if (= k 1)
       1
       (* k (ft ft (- k 1)))))))

; Part a
(defn fibonacci [n]
  (if (<= n 2)
    1
    ((fn [fib]
       (fib fib 1 1 n))
     (fn [ft x y k]
       (if (= k 2)
         y
         (ft ft y (+ x y) (- k 1)))))))

; Part b
(defn is-even? [x]
  ((fn [even? odd?]
     (even? even? odd? x))
   (fn [ev? od? n]
     (if (= n 0) true (od? ev? od? (- n 1))))
   (fn [ev? od? n]
     (if (= n 0) false (ev? ev? od? (- n 1))))))

;;; Exercise 4.22
(defn quoted?
  [exp]
  (tagged-list? exp 'quote))

(defn assignment?
  [exp]
  (tagged-list? exp 'set!))

(defn definition?
  [exp]
  (tagged-list? exp 'define))

(defn lambda?
  [exp]
  (tagged-list? exp 'lambda))

(defn let?
  [exp]
  (tagged-list? exp 'let))

(defn named-let?
  [exp]
  (symbol? (second exp)))

(defn let-body
  [exp]
  (if (named-let? exp)
    (nth exp 3)
    (nth exp 2)))

(defn let-variables
  [exp]
  (if (named-let? exp)
    (map first (nth exp 2))
    (map first (second exp))))

(defn let-values
  [exp]
  (if (named-let? exp)
    (map second (nth exp 2))
    (map second (second exp))))

(defn let-name
  [exp]
  (second exp))

(defn make-definition
  [fn-name parameters body]
  (list 'define (cons fn-name parameters) body))

(defn let->combination
  [exp]
  (let [parameters (let-variables exp)
        args (let-values exp)
        body (let-body exp)]
    (if (named-let? exp)
      (sequence->exp
       (list
        (make-definition (let-name exp)
                         parameters
                         body)
        (cons
         (let-name exp)
         args)))
      (cons
       (make-lambda (let-variables exp)
                    (list (let-body exp)))
       (let-values exp)))))

(defn analyze-let
  [exp]
  (analyze (let->combination exp)))

(defn begin?
  [exp]
  (tagged-list? exp 'begin))

(defn cond?
  [exp]
  (tagged-list? exp 'cond))

(defn analyze
  [exp]
  (cond (self-evaluating? exp)
        (analyze-self-evaluating exp)
        (quoted? exp) (analyze-quoted exp)
        (variable? exp) (analyze-variable exp)
        (assignment? exp) (analyze-assignment exp)
        (definition? exp) (analyze-definition exp)
        (lambda? exp) (analyze-lambda exp)
        (let? exp) (analyze-let exp)
        (begin? exp) (analyze-sequence (begin-actions exp))
        (cond? exp) (analyze (cond->if exp))
        (application? exp) (analyze-application exp)
        :else
        (Error. (str "Unknown expression type -- ANALYZE " exp))))

(defn my-eval
  [exp env]
  ((analyze exp) env))

(defn my-apply
  [procedure arguments]
  (cond (primitive-procedure? procedure)
          (apply-primitive-procedure procedure arguments)
        (compound-procedure? procedure)
          (eval-sequence
           (procedure-body procedure)
           (extend-environment
            (procedure-parameters procedure)
            arguments
            (procedure-environment procedure)))
        :else (Error. (str "Unknown procedure type -- APPLY " procedure))))

(defn fast-interpret [exp]
  (my-eval exp the-global-environment))


(def func
  '(define (add-positive x y)
     (if (or (< x 0) (< y 0)) (Error. "Must add positive numbers"))
     (if (= x 0)
       y
       (add-positive (- x 1) (+ y 1)))))

;(println "Time for unoptimized: ")
;(time (dotimes [x 30] (interpret '(add-positive 20 35))))

;(println "Time for optimized: ")
;(time (dotimes [x 30] (fast-interpret '(add-positive 20 35))))

;;; Exercise 4.26

(defn unless->if
  [pred conseq alt]
  (list 'if pred alt conseq))

(defn eval-unless
  [exp env eval]
  (eval (apply unless->if exp) env))

(def special-forms-with-unless
  (assoc pristine-special-forms :unless eval-unless))

(def eval-with-unless
  (make-eval special-forms-with-unless applicative-apply))


;;;; Exercise 4.28

(defn setup-environment
  []
  (let [initial-env
        (extend-environment (primitive-procedure-names)
                            (primitive-procedure-objects)
                            the-empty-environment)]
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    (define-variable! 'nil nil initial-env)
    initial-env))

(def the-global-environment (setup-environment))

(defrecord Thunk [exp env])

(defn atom?
  [x]
  (= clojure.lang.Atom (class x)))

(defn thunk?
  [obj]
  (if (atom? obj)
    (= Thunk (class @obj))
    false))

(defrecord Evaluated-Thunk [value])

(defn make-evaled-thunk
  [old-thunk new-value]
  (Evaluated-Thunk. new-value))

(defn evaluated-thunk?
  [obj]
  (if (atom? obj)
    (= Evaluated-Thunk (class @obj))))

(defn force-it
  [obj]
  (cond
    (thunk? obj)
    (let [result (actual-value (:exp @obj)
                               (:env @obj))]
      (swap! obj make-evaled-thunk result)
      result)
    (evaluated-thunk? obj) (:value @obj)
    :else obj))

(defn actual-value
  [exp env]
  (let [actual (my-eval exp env)
        forced (force-it actual)]
    forced))

(defn interpret
  [exp]
  (actual-value exp the-global-environment))

(interpret '(define (p f x y z)
              (f x y z)))

(interpret '(define (sum x y z)
             (+ x y z)))

;;; Exercise 4.32

(declare force-it actual-value)

(defprotocol Thinkable
  (force-thunk [_ eval]))

(deftype SimpleThunk [exp env])
(deftype CachedThunk [exp env])

(defn- force-simple-thunk [this eval]
  (actual-value (.exp this) (.env this) eval))

(extend SimpleThunk
  Thinkable
  {:force-thunk force-simple-thunk})

(extend CachedThunk
  Thinkable
  {:force-thunk (memoize force-simple-thunk)})

(defn actual-value
  [exp env eval]
  (force-it (eval exp env) eval))

(defn force-it
  [obj eval]
  (if (satisfies? Thinkable obj)
    (force-thunk obj eval)
    obj))

(deftype NonStrictPrimitive [fn]
  Appliable
  (my-apply [this args env eval]
    (apply (.fn this) (map #(actual-value % env eval) args))))

(deftype NonStrictProcedure [params body env]
  Appliable
  (my-apply [this args env eval]
    (let [env (env-extend (.env this)
                          (zipmap (.params this)
                                  (map #(CachedThunk. % env) args)))]
      ((eval-seq eval) (.body this) env))))

(defn normative-apply
  [exp env eval]
  (let [proc (actual-value (first exp) env eval)
        args (rest exp)]
    (my-apply proc args env eval)))

(defn eval-lambda-non-strict
  [[params & body] env _]
  (NonStrictProcedure. params body env))

(defn eval-if-lazy
  [[pred conseq alt] env eval]
  (if (actual-value pred env eval)
    (eval conseq env)
    (eval alt    env)))

(def pristine-special-forms-lazy
  (assoc pristine-special-forms
    :lambda eval-lambda-non-strict
    :if     eval-if-lazy))

(def pristine-primitives-non-strict
  (let [m pristine-primitives-map]
    (into {} (for [[k v] m] [k (NonStrictPrimitive. v)]))))

(def pristine-eval-lazy
  (make-eval pristine-special-forms-lazy normative-apply))

(defn maybe-delay
  [arg param env eval]
  (cond (symbol? param) (actual-value arg env eval)
        (= 'lazy (second param)) (SimpleThunk. arg env)
        (= 'lazy-memo (second param)) (CachedThunk. arg env)))

(defn get-param-symbol
  [param]
  (if (symbol? param)
    param
    (first param)))

(deftype MixedProcedure [params body env]
  Appliable
  (my-apply [this args env eval]
    (let [params (.params this)
          env (env-extend (.env this)
                          (zipmap (map get-param-symbol params)
                                  (map #(maybe-delay %1 %2 env eval)
                                       args
                                       params)))]
      ((eval-seq eval) (.body this) env))))

(defn eval-lambda-mixed
  [[params & body] env _]
  (MixedProcedure. params body env))

(def pristine-special-forms-mixed
  (assoc pristine-special-forms
    :lambda eval-lambda-mixed))

(def pristine-eval-mixed
  (make-eval pristine-special-forms-mixed normative-apply))

;; amb evaluator

(declare amb-analyze-apply)

(defn make-amb-analyze
  [analyzors]
  (fn ! [exp]
    (cond (self-eval? exp)
          (fn [env succeed fail]
            (succeed exp fail))
          (variable? exp)
          (fn [env succeed fail]
            (succeed (env-lookup env exp) fail))
          :else
          (let [[op & rest] exp
                op (keyword op)]
            (if (contains? analyzors op)
              ;; special form analyzors
              ((get analyzors op) rest !)
              ;; application
              (amb-analyze-apply exp !))))))

(defn amb-analyze-seq
  [analyze]
  (fn [coll]
    (let [sequentially
          (fn [a b]
            (fn [env succeed fail]
              (a env
                 (fn [a-val fail]
                   (b env succeed fail))
                 fail)))
          procs (map analyze coll)]
      (if (empty? procs)
        (throw (Exception. "Empty sequence -- ANALYZE"))
        (loop [head (first procs)
               next (rest  procs)]
          (if (empty? next)
            head
            (recur (sequentially head (first next))
                   (rest next))))))))

;; basic amb special form analyzors

(defn amb-analyze-quote [[x] _]
  (fn [env succeed fail]
    (succeed x fail)))

(defn amb-analyze-lambda
  [[params & body] analyze]
  (fn [env succeed fail]
    (succeed (Procedure. params
                         ((amb-analyze-seq analyze) body)
                         env)
             fail)))

(defn amb-analyze-if
  [[pred conseq alt] analyze]
  (let [pred   (analyze pred)
        conseq (analyze conseq)
        alt    (analyze alt)]
    (fn [env succeed fail]
      (pred env
            ;; success continuation
            (fn [pred-value fail]
              (if pred-value
                (conseq env succeed fail)
                (alt    env succeed fail)))
            ;; failure continuation
            fail))))

(defn amb-analyze-define
  [exp analyze]
  (if (symbol? (first exp))
    (let [[v o] exp
          o (analyze o)]
      (fn [env succeed fail]
        (o env
           (fn [val fail]
             (env-define! env v val)
             (succeed 'ok fail))
           fail)))
    (analyze (apply desugar-define exp))))

(defn amb-analyze-assign
  [[v o] analyze]
  (let [o (analyze o)]
    (fn [env succeed fail]
      (o env
         (fn [val fail]
           (let [old-val (env-lookup env v)]
             (env-set! env v val)
             (succeed 'ok
                      ;; undo assignment
                      (fn []
                        (env-set! env v old-val)
                        (fail)))))
         fail))))

(defprotocol AmbAppliable
  (amb-apply [this args succeed fail]))

(extend-protocol AmbAppliable
  Procedure
  (amb-apply [this args succeed fail]
    (let [env (env-extend (.env this)
                          (zipmap (.params this) args))]
      ((.body this) env succeed fail)))
  Primitive
  (amb-apply [this args succeed fail]
    (succeed (my-apply this args nil nil) fail)))

(defn amb-get-args
  [aprocs env succeed fail]
  (if (empty? aprocs)
    (succeed '() fail)
    ((first aprocs)
     env
     (fn [arg fail]
       (amb-get-args (rest aprocs)
                     env
                     (fn [args fail]
                       (succeed (cons arg args)
                                fail))
                     fail))
     fail)))

(defn amb-analyze-apply
  [exp analyze]
  (let [[proc & args] (map analyze exp)]
    (fn [env succeed fail]
      (proc env
            (fn [proc fail]
              (amb-get-args args
                            env
                            (fn [args fail]
                              (amb-apply proc
                                         args
                                         succeed
                                         fail))
                            fail))
            fail))))

(defn amb-analyze-amb
  [choices analyze]
  (let [cprocs (map analyze choices)]
    (fn [env succeed fail]
      (letfn [(try-next [choices]
                (if (empty? choices)
                  (fail)
                  ((first choices)
                   env
                   succeed
                   #(try-next (rest choices)))))]
        (try-next cprocs)))))

(defn amb-analyze-begin
  [coll analyze]
  ((amb-analyze-seq analyze) coll))

(defn amb-analyze-let
  [exp analyze]
  (analyze (apply let->combination exp)))

(def pristine-amb-analyzors
  {:quote  amb-analyze-quote
   :set!   amb-analyze-assign
   :define amb-analyze-define
   :if     amb-analyze-if
   :lambda amb-analyze-lambda
   :begin  amb-analyze-begin
   :let    amb-analyze-let
   :amb    amb-analyze-amb})

(defn amb-eval
  [exp env succeed fail]
  (let [analyze (make-amb-analyze pristine-amb-analyzors)]
    ((analyze exp) env succeed fail)))

(def amb-utils
  '((define (require p) (if (not p) (amb)))
    (define (an-element-of items)
      (require (not (null? items)))
      (amb (car items) (an-element-of (cdr items))))))

(defn amb-let-helper
  [bindings body]
  (if (< 0 (count bindings))
    (let [[form expression] (take 2 bindings)
          more-bindings (drop 2 bindings)
          filtered-recurse (if (= :where (first more-bindings))
                             `(when ~(second more-bindings)
                                ~(amb-let-helper (drop 2 more-bindings) body))
                             (amb-let-helper more-bindings body))
          res (if  (and (seq? expression)
                        (= 'amb (first expression)))
                `(apply concat (for [~form ~(second expression)]
                                 ~filtered-recurse))
                `(let [~form ~expression]
                   ~filtered-recurse))]
      res)
    [body]))

(defmacro amb-let [bindings body]
  "vaguely like let, except
   -- if the expression bound to a variable is of the form
      (amb col), this has the semantics that the value of the variable
      is one of the members of the collection
   -- following the binding form, we accept a vector of requirements
      each of which a vector whose first is a set of variables to which
      it applies, and whose second is an expression depending on those vars
   -- we return a lazy seq of the values produced by the let for variable
      assignments which satisfy the requirements"
  (amb-let-helper bindings body))

;;; Exercise 4.35

(def an-integer-between
  '(define (an-integer-between low high)
     (require (< low high))
     (amb low (an-integer-between (+ low 1) high))))

;;; Exercise 4.36

(def amb-pythagorean-triples
  (amb-let
   [k (amb (drop 5 (range)))
    i (amb (range 2 k))
    j (amb (range i k))
    :where (= (+ (* i i) (* j j)) (* k k))]
   [i j k]))

;;; Exercise 4.38

;; multiple dwelling puzzle:

(def multiple-dwelling
  (amb-let [baker (amb [1 2 3 4 5])
            :where (not (= baker 5))
            cooper (amb [1 2 3 4 5])
            :where (not (= cooper 1))
            fletcher (amb [1 2 3 4 5])
            :where (and (not (= fletcher 5))
                        (not (= fletcher 1)))
            miller (amb [1 2 3 4 5])
            :where (> miller cooper)
            smith (amb [1 2 3 4 5])
            :where (and (distinct? baker cooper fletcher miller smith)
                        (not (= (Math/abs (- smith fletcher)) 1))
                        (not (= (Math/abs (- fletcher cooper)) 1)))]
           [:baker baker
            :cooper cooper
            :fletcher fletcher
            :miller miller
            :smith smith]))

;; modified version

(def multiple-dwelling-1
  (amb-let [baker (amb [1 2 3 4 5])
            :where (not (= baker 5))
            cooper (amb [1 2 3 4 5])
            :where (not (= cooper 1))
            fletcher (amb [1 2 3 4 5])
            :where (and (not (= fletcher 5))
                        (not (= fletcher 1)))
            miller (amb [1 2 3 4 5])
            :where (> miller cooper)
            smith (amb [1 2 3 4 5])
            :where (distinct? baker cooper fletcher miller smith)]
           [:baker baker
            :cooper cooper
            :fletcher fletcher
            :miller miller
            :smith smith]))

;;; Exercise 4.40

(def multiple-dwelling-2
  (amb-let [baker    (amb [1 2 3 4])
            cooper   (amb [2 3 4 5])
            fletcher (amb [2 3 4])
            miller   (amb [1 2 3 4 5])
            :where (> miller cooper)
            smith (amb [1 2 3 4 5])
            :where (and (distinct? baker cooper fletcher miller smith)
                        (not (= (Math/abs (- smith fletcher)) 1))
                        (not (= (Math/abs (- fletcher cooper)) 1)))]
           [:baker baker
            :cooper cooper
            :fletcher fletcher
            :miller miller
            :smith smith]))

;;; Exercise 4.41

(defn multiple-dwelling-ordinary []
  (let [permutations (combo/permutations [1 2 3 4 5])]
    (loop [perm   permutations
           result ()]
      (if (empty? perm)
        result
        (let [[baker cooper fletcher miller smith] (first perm)]
          (if (and (not= baker 5)
                   (not= cooper 1)
                   (not= fletcher 5)
                   (not= fletcher 1)
                   (> miller cooper)
                   (not (= (Math/abs (- smith fletcher)) 1))
                   (not (= (Math/abs (- fletcher cooper)) 1)))
            (recur (rest perm)
                   (cons (into [] (interleave
                                   [:baker :cooper :fletcher :miller :smith]
                                   (first perm)))
                         result))
            (recur (rest perm) result)))))))

;;; Exercise 4.42

(defn xor
  [a b]
  (or (and a (not b)) (and b (not a))))

(def liar-puzzle
  (amb-let [betty (amb [1 2 3 4 5])
            ethel (amb [1 2 3 4 5])
            joan  (amb [1 2 3 4 5])
            kitty (amb [1 2 3 4 5])
            mary  (amb [1 2 3 4 5])
            :where (and (distinct? betty ethel joan kitty mary)
                        (xor (= kitty 2) (= betty 3))
                        (xor (= ethel 1) (= joan  2))
                        (xor (= joan  3) (= ethel 5))
                        (xor (= kitty 2) (= mary  4))
                        (xor (= mary  4) (= betty 1)))]
           [:betty betty
            :ethel ethel
            :joan  joan
            :kitty kitty
            :mary  mary]))

;;; Exercise 4.43

(def yacht-puzzle
  (amb-let [mary      :moore
            melissa   :barnacle
            lorna     (amb [:downing :hall :parker])
            gabrielle (amb [:downing :hall :parker])
            rosalind  (amb [:downing :parker])
            :where (and (distinct? lorna gabrielle rosalind)
                        ;; Gabrielle's father owns yacht
                        ;; named after Parker's daughter
                        (= :parker
                           (gabrielle {:downing melissa
                                       :hall    rosalind
                                       :parker  mary})))]
           lorna))

(def yacht-puzzle-1
  (->>
   (amb-let [melissa   :barnacle
             mary      (amb [:moore :downing :hall])
             lorna     (amb [:downing :hall :parker])
             gabrielle (amb [:moore :downing :hall :parker])
             rosalind  (amb [:moore :downing :parker])
             :where (and (distinct? mary lorna gabrielle rosalind)
                         (= :parker
                            (gabrielle {:moore   lorna
                                        :downing melissa
                                        :hall    rosalind
                                        :parker  mary})))]
            lorna)
   (into #{})))

;;; Exercise 4.44

(defn queen-safe?
  [positions]
  (let [new-col (count positions)
        new-row (last positions)]
    (every? identity
            (for [[col row]
                  ;; sequence of pair (col, row)
                  (zipmap (range 1 (count positions))
                          (drop-last positions))]
              (and (not= row new-row)
                   ;; diagonal attack
                   (not= (- new-col col)
                         (Math/abs (- new-row row))))))))

(defn amb-solve-8-queens []
  (amb-let [q1 (amb (range 1 9))
            q2 (amb (range 1 9))
            :where (queen-safe? [q1 q2])
            q3 (amb (range 1 9))
            :where (queen-safe? [q1 q2 q3])
            q4 (amb (range 1 9))
            :where (queen-safe? [q1 q2 q3 q4])
            q5 (amb (range 1 9))
            :where (queen-safe? [q1 q2 q3 q4 q5])
            q6 (amb (range 1 9))
            :where (queen-safe? [q1 q2 q3 q4 q5 q6])
            q7 (amb (range 1 9))
            :where (queen-safe? [q1 q2 q3 q4 q5 q6 q7])
            q8 (amb (range 1 9))
            :where (queen-safe? [q1 q2 q3 q4 q5 q6 q7 q8])]
           [q1 q2 q3 q4 q5 q6 q7 q8]))

;;; Exercise 4.50

(defn amb-analyze-ramb
  [choices analyze]
  (amb-analyze-amb (shuffle choices) analyze))

(def ramb-analyzors
  (assoc pristine-amb-analyzors
    :ramb amb-analyze-ramb))

(defn ramb-eval
  [exp env succeed fail]
  (let [analyze (make-amb-analyze ramb-analyzors)]
    ((analyze exp) env succeed fail)))

;;; Exercise 4.51

(defn amb-analyze-permanent-assign
  [[v o] analyze]
  (let [o (analyze o)]
    (fn [env succeed fail]
      (o env
         (fn [val fail]
           (env-set! env v val)
           (succeed 'ok fail))
         fail))))

(def permanent-assign-amb-analyzors
  (assoc pristine-amb-analyzors
    :permanent-set! amb-analyze-permanent-assign))

(defn permanent-set-amb-eval
  [exp env succeed fail]
  (let [analyze (make-amb-analyze permanent-assign-amb-analyzors)]
    ((analyze exp) env succeed fail)))

;;; Exercise 4.52

(defn amb-analyze-if-fail
  [[conseq recover] analyze]
  (let [conseq  (analyze conseq)
        recover (analyze recover)]
    (fn [env succeed fail]
      (conseq env
              succeed
              #(recover env succeed fail)))))

(def if-fail-amb-analyzors
  (assoc pristine-amb-analyzors
    :if-fail amb-analyze-if-fail))

(defn if-fail-amb-eval
  [exp env succeed fail]
  (let [analyze (make-amb-analyze if-fail-amb-analyzors)]
    ((analyze exp) env succeed fail)))

;;; Exercise 4.53

(def amb-analyzors-for-4-53
  (assoc pristine-amb-analyzors
    :permanent-set! amb-analyze-permanent-assign
    :if-fail amb-analyze-if-fail))

(defn amb-eval-for-4-53
  [exp env succeed fail]
  (let [analyze (make-amb-analyze amb-analyzors-for-4-53)]
    ((analyze exp) env succeed fail)))

;;; Exercise 4.54

(defn amb-analyze-require
  [[pred] analyze]
  (let [pred (analyze pred)]
    (fn [env succeed fail]
      (pred env
            (fn [pred-value fail2]
              (if-not pred-value
                (fail2)
                (succeed 'ok fail2)))
            fail))))

(def special-require-amb-analyzors
  (assoc pristine-amb-analyzors
    :require amb-analyze-require))

(defn special-require-amb-eval
  [exp env succeed fail]
  (let [analyze (make-amb-analyze special-require-amb-analyzors)]
    ((analyze exp) env succeed fail)))

;; Sample data base as is in 4.4.1

(defrel address p a)
(defrel job p j)
(defrel salary p s)
(defrel salary p s)
(defrel supervisor p s)
(defrel can-do-job p j)

(def facts
  (db
   [address [:Bitdiddle :Ben] [:Slumerville [:Ridge :Road] 10]]
   [job     [:Bitdiddle :Ben] [:computer :wizard]]
   [salary  [:Bitdiddle :Ben] 60000]
   [supervisor [:Bitdiddle :Ben] [:Warbucks :Oliver]]

   [address    [:Hacker :Alyssa :P] [:Cambridge [:Mass :Ave] 78]]
   [job        [:Hacker :Alyssa :P] [:computer :programmer]]
   [salary     [:Hacker :Alyssa :P] 40000]
   [supervisor [:Hacker :Alyssa :P] [:Bitdiddle :Ben]]

   [address    [:Fect :Cy :D] [:Cambridge [:Ames :Street] 3]]
   [job        [:Fect :Cy :D] [:computer :programmer]]
   [salary     [:Fect :Cy :D] 35000]
   [supervisor [:Fect :Cy :D] [:Bitdiddle :Ben]]

   [address    [:Tweakit :Lem :E] [:Boston [:Bay :State :Road] 22]]
   [job        [:Tweakit :Lem :E] [:computer :technician]]
   [salary     [:Tweakit :Lem :E] 25000]
   [supervisor [:Tweakit :Lem :E] [:Bitdiddle :Ben]]

   [address    [:Reasoner :Louis] [:Slumerville [:Pine :Tree :Road] 80]]
   [job        [:Reasoner :Louis] [:computer :programmer :trainee]]
   [salary     [:Reasoner :Louis] 30000]
   [supervisor [:Reasoner :Louis] [:Hacker :Alyssa :P]]

   [address    [:Warbucks :Oliver] [:Swellesley [:Top :Heap :Road]]]
   [job        [:Warbucks :Oliver] [:administration :big :wheel]]
   [salary     [:Warbucks :Oliver] 150000]

   [address    [:Scrooge :Eben] [:Weston [:Shady :Lane] 10]]
   [job        [:Scrooge :Eben] [:accounting :chief :accountant]]
   [salary     [:Scrooge :Eben] 75000]
   [supervisor [:Scrooge :Eben] [:Warbucks :Oliver]]

   [address    [:Cratchet :Robert] [:Allston [:N :Harvard :Street] 16]]
   [job        [:Cratchet :Robert] [:accounting :scrivener]]
   [salary     [:Cratchet :Robert] 18000]
   [supervisor [:Cratchet :Robert] [:Scrooge :Eben]]

   [address    [:Aull :DeWitt] [:Slumerville [:Onion :Square] 5]]
   [job        [:Aull :DeWitt] [:administration :secretary]]
   [salary     [:Aull :DeWitt] 25000]
   [supervisor [:Aull :DeWitt] [:Warbucks :Oliver]]

   [can-do-job [:computer :wizard] [:computer :programmer]]
   [can-do-job [:computer :wizard] [:computer :technician]]
   [can-do-job [:computer :programmer] [:computer :programmer :trainee]]
   [can-do-job [:administration :secretary] [:administration :big :wheel]]))

;;; Exercise 4.55

(def supervised-by-ben-bitdiddle
  "all people supervised by Ben Bitdiddle"
  (run-db* facts [q] (supervisor q [:Bitdiddle :Ben])))

(def people-in-accounting-division
  "the names and jobs of all people in the accounting division"
  (run-db* facts [q]
           (fresh [?name ?job]
                  (job ?name ?job)
                  (firsto ?job :accounting)
                  (== q [?name ?job]))))

(def people-in-slumerville
  "the names and addresses of all people who live in Slumerville"
  (run-db* facts [q]
           (fresh [?name ?address]
                  (address ?name ?address)
                  (firsto ?address :Slumerville)
                  (== q [?name ?address]))))

;;; Exercise 4.56

(def supervised-by-ben-bitdiddle-with-address
  "the names of all people who are supervised by Ben Bitdiddle,
   together with their addresses"
  (run-db* facts [q]
           (fresh [?name ?address]
                  (supervisor ?name [:Bitdiddle :Ben])
                  (address ?name ?address)
                  (== q [?name ?address]))))

(def salary-less-than-ben-bitdiddle-s
  "all people whose salary is less than Ben Bitdiddle's,
   together with their salary and Ben Bitdiddle's salary"
  (run-db* facts [q]
           (fresh [?name ?salary ?ben-salary]
                  (salary [:Bitdiddle :Ben] ?ben-salary)
                  (salary ?name ?salary)
                  (fd/< ?salary ?ben-salary)
                  (== q [?name ?salary ?ben-salary]))))

(def supervised-not-in-computer-division
  "all people who are supervised by someone who is not in the
   computer division, together with the supervisor's name and job"
  (run-db* facts [q]
           (fresh [?name ?supervisor ?supervisor-job]
                  (supervisor ?name ?supervisor)
                  (job ?supervisor ?supervisor-job)
                  (nafc firsto ?supervisor-job :computer)
                  (== q [?name ?supervisor ?supervisor-job]))))

;;; Exercise 4.57

(defne can-replace
  "A rule that says that person 1 can replace person 2 if
   either person 1 does the same job as person 2 or someone
   who does person 1's job can also do person 2's job,
   and if person 1 and person 2 are not the same person."
  [?p1 ?p2]
  ([_ _] (fresh [?job1 ?job2]
                (job ?p1 ?job1)
                (job ?p2 ?job2)
                (nafc == ?p1 ?p2)
                (conde [(== ?job1 ?job2)]
                       [(can-do-job ?job1 ?job2)]))))

(def can-replace-cy-d-fect
  "All people who can replace Cy D. Fect"
  (run-db* facts [q]
           (can-replace q [:Fect :Cy :D])))

(def can-replace-who-is-being-paid-more
  "All people who can replace someone who is being paid more than
   they are, together with the two salaries."
  (run-db* facts [q]
           (fresh [?p1 ?p2 ?s1 ?s2]
                  (can-replace ?p1 ?p2)
                  (salary ?p1 ?s1)
                  (salary ?p2 ?s2)
                  (fd/< ?s1 ?s2)
                  (== q [?p1 ?s1 ?s2]))))

;;; Exercise 4.58

(defne big-shot
  "A person is a ``big shot'' in a division if the person works in the
   division but does not have a supervisor who works in the division."
  [?p ?div]
  ([_ _] (fresh [?sv ?job1 ?job2]
                (job ?p ?job1)
                (firsto ?job1 ?div)
                (supervisor ?p ?sv)
                (job ?sv ?job2)
                (nafc firsto ?job2 ?div))))


;;; Exercise 4.59

(defrel meeting d t)

(def meetings
  (db
   [meeting :accounting [:Monday :9am]]
   [meeting :administration [:Monday :3pm]]
   [meeting :computer [:Wednesday :3pm]]
   [meeting :administration [:Friday :1pm]]
   [meeting :whole-company [:Wednesday :4pm]]))

(def meetings-at-friday
  (run-db* meetings [q]
           (fresh [?div ?day-and-time]
                  (meeting ?div ?day-and-time)
                  (firsto ?day-and-time :Friday)
                  (== q [?div ?day-and-time]))))

(defne meeting-time
  [?person ?day-and-time]
  ([_ _] (fresh [?job ?div]
                (conde [(job ?person ?job)
                        (firsto ?job ?div)
                        (meeting ?div ?day-and-time)]
                       [(meeting :whole-company ?day-and-time)]))))

(def alyssa-meetings-at-wednesday
  (with-dbs [facts meetings]
    (run* [q]
          (fresh [?div ?day-and-time]
                 (meeting ?div ?day-and-time)
                 (firsto ?day-and-time :Wednesday)
                 (meeting-time [:Hacker :Alyssa :P] ?day-and-time)
                 (== q [?div ?day-and-time])))))

;;; Exercise 4.60

(defne asymmetric-lives-near
  [?p1 ?p2]
  ([_ _] (fresh [?a1 ?a2 ?t]
                (address ?p1 ?a1)
                (address ?p2 ?a2)
                (firsto ?a1 ?t)
                (firsto ?a2 ?t)
                (project [?p1 ?p2]
                         (== true (neg? (compare ?p1 ?p2)))))))

;;; Exercise 4.61

(defne next-to
  "A relation where l is a collection, such that x and y are adjacent."
  [x y l]
  ([_ _ [x y . tail]])
  ([_ _ [v . tail]]
     (next-to x y tail)))

;;; Exercise 4.62

(defne last-pair
  "A relation where l is a seq, such that x is the last pair in it."
  [l x]
  ([[_ . ()] l])
  ([[_ . tail] _]
     (last-pair tail x)))

;;; Exercise 4.63

(defrel son x y)
(defrel wife x y)

(def generations-of-adam
  (db
   [son :Adam :Cain]
   [son :Cain :Enoch]
   [son :Enoch :Irad]
   [son :Mehujael :Methushael]
   [son :Methushael :Lamech]
   [wife :Lamech :Ada]
   [son :Ada :Jabal]
   [son :Ada :Jubal]))

(defne son-of
  [x y]
  ([_ _] (fresh [w] (wife x w) (son w y)))
  ([_ _] (son x y)))

(defne grandson-of
  [x y]
  ([_ _] (fresh [z] (son x z) (son-of z y))))

;;; Exercise 4.68

(defne reverseo
  "A relation where l is a seq, such that x is the reverse order of l."
  [l x]
  ([[] []])
  ([[head . tail] _]
     (fresh [q]
            (reverseo tail q)
            (appendo q [head] x))))

;; `(run* [q] (reverseo '(1 2 3) q))` works as expected,
;; whereas `(run* [q] (reverseo q '(1 2 3)))` falls into infinite loop.

;;; The Implementation of Query System

(def ^:dynamic ^:private *assertions* (atom {}))
(def ^:dynamic ^:private *rules* (atom {}))

;; Query Syntax Procedures

(defn assertion-to-be-added?
  [exp] (and (seq? exp) (= 'assert! (first exp))))

(defn assertion-body
  [[_ body]] body)

(defn rule?
  [statement]
  (and (seq? statement) (= 'rule (first statement))))

(defn rule-conclusion
  [[_ conclusion body]] conclusion)

(defn rule-body
  [[_ conclusion body]] (if body body '(always-true)))

(defn make-logic-var
  [symbol] (with-meta symbol {:logic-var true}))

(defn map-over-symbols
  [proc exp]
  (cond (seq? exp)
        (if (empty? exp)
          exp
          (cons (map-over-symbols proc (first exp))
                (map-over-symbols proc (rest  exp))))
        (symbol? exp) (proc exp)
        :else exp))

(defn expand-question-mark
  [symbol]
  (let [chars (str symbol)]
    (if (= \? (first chars))
      (make-logic-var symbol)
      symbol)))

(defn query-syntax-process
  [exp] (map-over-symbols expand-question-mark exp))

(defn logic-var?
  [exp] (and (symbol? exp) (true? (:logic-var (meta exp)))))

(defn constant-symbol?
  [exp] (and (symbol? exp) (nil? (:logic-var (meta exp)))))

;; Stream operations

(defn stream-append-delayed
  [s1 delayed-s2]
  (lazy-seq
   (if (empty? s1)
     (force delayed-s2)
     (cons (first s1) (stream-append-delayed (rest s1) delayed-s2)))))

(defn interleave-delayed
  [s1 delayed-s2]
  (seq
   (lazy-seq
    (if (empty? s1)
      (force delayed-s2)
      (cons (first s1)
            (interleave-delayed (force delayed-s2) (delay (rest s1))))))))

(defn flatten-stream
  [stream]
  (if (empty? stream)
    ()
    (interleave-delayed
     (first stream) (delay (flatten-stream (rest stream))))))

(defn stream-flatmap
  [proc s] (flatten-stream (map proc s)))

;; Maintaining the Data Base

(defn indexable?
  [pat] (symbol? (first pat)))

(defn index-key-of [pat]
  (let [key (first pat)]
    (if (logic-var? key) '? key)))

(defn use-index?
  [pat] (constant-symbol? (first pat)))

(defn store-assertion-in-index
  [assertion]
  (if (indexable? assertion)
    (let [key (index-key-of assertion)
          current-assertion-stream (get @*assertions* key)]
      (swap! *assertions* assoc key (cons assertion
                                          current-assertion-stream)))))

(defn store-rule-in-index
  [rule]
  (let [pattern (rule-conclusion rule)]
    (if (indexable? pattern)
      (let [key (index-key-of pattern)
            current-rule-stream (get @*rules* key)]
        (swap! *rules* assoc key (cons rule
                                       current-rule-stream))))))

(defn add-assertion!
  [assertion] (store-assertion-in-index assertion) :ok)

(defn add-rule!
  [rule] (store-rule-in-index rule) :ok)

(defn get-all-assertions
  [] (apply concat (vals @*assertions*)))

(defn get-indexed-assertions
  [pattern] (get @*assertions* (index-key-of pattern)))

(defn fetch-assertions
  [pattern frame]
  (if (use-index? pattern)
    (get-indexed-assertions pattern)
    (get-all-assertions)))

(defn get-all-rules
  [] (apply concat (vals @*rules*)))

(defn get-indexed-rules
  [pattern] (concat (get @*rules* (index-key-of pattern))
                    (get @*rules* '?)))

(defn fetch-rules
  [pattern frame]
  (if (use-index? pattern)
    (get-indexed-rules pattern)
    (get-all-rules)))

(defn add-rule-or-assertion!
  [assertion]
  (if (rule? assertion)
    (add-rule! assertion)
    (add-assertion! assertion)))

;; Rules and Unification

(declare extend-if-possible)

(defn unify-match
  [p1 p2 frame]
  (cond (= frame :failed) :failed
        (= p1 p2) frame
        (logic-var? p1) (extend-if-possible p1 p2 frame)
        (logic-var? p2) (extend-if-possible p2 p1 frame)
        (and (seq? p1) (seq? p2))
        (cond
         (= '. (first p1) (first p2))
         (recur (second p1) (second p2) frame)
         (= '. (first p1))
         (recur (second p1) p2 frame)
         (= '. (first p2))
         (recur p1 (second p2) frame)
         :else
         (recur (rest p1)
                (rest p2)
                (unify-match (first p1)
                             (first p2)
                             frame)))
        :else :failed))

(defn depends-on?
  [exp var frame]
  (letfn [(tree-walk [e]
            (cond (logic-var? e)
                  (if (= e var)
                    true
                    (if-let [v (get frame e)]
                      (tree-walk v)
                      false))
                  (seq? e)
                  (if (empty? e)
                    false
                    (or (tree-walk (first e))
                        (tree-walk (rest  e))))
                  :else false))]
    (tree-walk exp)))

(defn extend-if-possible
  [left right frame]
  (let [val (get frame left)]
    (cond val (unify-match val right frame)
          (logic-var? right) (if-let [val (get frame right)]
                               (unify-match left val frame)
                               (assoc frame left right))
          (depends-on? right left frame) :failed
          :else (assoc frame left right))))

(defn rename-variables-in
  [rule]
  (let [rule-app-id (gensym "")]
    (letfn [(tree-walk [exp]
              (cond
               (logic-var? exp) (make-logic-var
                                 (symbol (str exp \- rule-app-id)))
               (seq? exp) (if (empty? exp)
                            exp
                            (cons (tree-walk (first exp))
                                  (tree-walk (rest  exp))))
               :else exp))]
      (tree-walk rule))))

(defn apply-a-rule
  [rule query-pattern query-frame qeval]
  (let [clean-rule   (rename-variables-in rule)
        unify-result (unify-match query-pattern
                                  (rule-conclusion clean-rule)
                                  query-frame)]
    (if (= unify-result :failed)
      ()
      (qeval (rule-body clean-rule)
             (list unify-result)))))

(defn apply-rules
  [pattern frame qeval]
  (stream-flatmap #(apply-a-rule % pattern frame qeval)
                  (fetch-rules pattern frame)))

;; Finding assertions by Pattern Matching

(declare extend-if-consistent)

(defn pattern-match
  [pat dat frame]
  (cond
   (= frame :failed) :failed
   (= pat dat)       frame
   (logic-var? pat)  (extend-if-consistent pat dat frame)
   (and (seq? pat) (seq? dat))
   ;; handle patterns with dotted tails
   (cond
    (= '. (first pat) (first dat))
    (recur (second pat) (second dat) frame)
    (= '. (first pat))
    (recur (second pat) dat frame)
    (= '. (first dat))
    (recur pat (second dat) frame)
    :else
    (recur (rest pat)
           (rest dat)
           (pattern-match (first pat)
                          (first dat)
                          frame)))
   :else :failed))

(defn extend-if-consistent
  [var dat frame]
  (if-let [val (get frame var)]
    (pattern-match val dat frame)
    (assoc frame var dat)))

(defn check-an-assertion
  [assertion query-pat query-frame]
  (let [match-result
        (pattern-match query-pat assertion query-frame)]
    (if (= match-result :failed)
      ()
      (list match-result))))

(defn find-assertions
  "Returns a stream of frames, each extending the given one by a
   data-base match of the give pattern."
  [pattern frame]
  (stream-flatmap #(check-an-assertion % pattern frame)
                  (fetch-assertions pattern frame)))

;; simple queries

(defn simple-query
  [query-pattern frames qeval]
  (stream-flatmap
   #(stream-append-delayed
     (find-assertions query-pattern %)
     (delay (apply-rules query-pattern % qeval)))
   frames))

;; compound queries

(defn qeval-conjoin
  [conjuncts frames qeval]
  (if (empty? conjuncts)
    frames
    (recur (rest conjuncts)
           (qeval (first conjuncts) frames)
           qeval)))

(defn qeval-disjoin
  [disjuncts frames qeval]
  (if (empty? disjuncts)
    ()
    (interleave-delayed
     (qeval (first disjuncts) frames)
     (delay (qeval-disjoin (rest disjuncts) frames qeval)))))

;; filters

(defn qeval-negate
  [[negated-query & _] frames qeval]
  (stream-flatmap
   #(if (empty? (qeval negated-query (list %))) (list %) ())
   frames))

(declare instantiate)

(defn qeval-lisp-value
  [call frames qeval]
  (letfn [(exec [[pred & args]]
            (apply (eval pred) args))
          (error [v f]
            (throw (Exception.
                    (print-str "Unknown pat var -- LISP-VALUE" v))))]
    (stream-flatmap
     #(if (exec (instantiate call % error)) (list %) ()) frames)))

(defn qeval-always-true [_ frames qeval] frames)

(def qeval-basic-special-forms
  {:and         qeval-conjoin
   :or          qeval-disjoin
   :not         qeval-negate
   :lisp-value  qeval-lisp-value
   :always-true qeval-always-true})

;; The Driver Loop and Instantiation

(defn instantiate
  [exp frame unbound-var-handler]
  (letfn
      [(copy [exp]
         (cond (logic-var? exp)
               ;; look up variable in the frame
               (if-let [val (get frame exp)]
                 (recur val)
                 (unbound-var-handler exp frame))
               (seq? exp)
               ;; handle dotted list
               (cond (empty? exp) exp
                     (= '. (first exp)) (copy (second exp))
                     :else (cons (copy (first exp))
                                 (copy (rest  exp))))
               :else exp))]
    (copy exp)))

(defn make-qeval
  [special-forms]
  (letfn [(qeval [[op & args :as query] frames]
            (if-let [qproc (get special-forms (keyword op))]
              (qproc args frames qeval)
              (simple-query query frames qeval)))
          (driver-loop [queries result]
            (if (empty? queries)
              result
              (let [q (query-syntax-process (first queries))]
                (if (assertion-to-be-added? q)
                  (do
                    (add-rule-or-assertion! (assertion-body q))
                    (recur (rest queries) :ok))
                  (do
                    (recur (rest queries)
                           (map #(instantiate q % (fn [v f] v))
                                (qeval q '({})))))))))]
    (fn [queries]
      (binding [*assertions* (atom {})
                *rules*      (atom {})]
        (driver-loop queries nil)))))

(def qeval
  (make-qeval qeval-basic-special-forms))

(def facts-1
  "Facts about Microshaft, `qeval` style"
  '((assert! (address (Bitdiddle Ben) (Slumerville (Ridge Road) 10)))
    (assert! (job (Bitdiddle Ben) (computer wizard)))
    (assert! (salary (Bitdiddle Ben) 60000))
    (assert! (address (Hacker Alyssa P) (Cambridge (Mass Ave) 78)))
    (assert! (job (Hacker Alyssa P) (computer programmer)))
    (assert! (salary (Hacker Alyssa P) 40000))
    (assert! (supervisor (Hacker Alyssa P) (Bitdiddle Ben)))
    (assert! (address (Fect Cy D) (Cambridge (Ames Street) 3)))
    (assert! (job (Fect Cy D) (computer programmer)))
    (assert! (salary (Fect Cy D) 35000))
    (assert! (supervisor (Fect Cy D) (Bitdiddle Ben)))
    (assert! (address (Tweakit Lem E) (Boston (Bay State Road) 22)))
    (assert! (job (Tweakit Lem E) (computer technician)))
    (assert! (salary (Tweakit Lem E) 25000))
    (assert! (supervisor (Tweakit Lem E) (Bitdiddle Ben)))
    (assert! (address (Reasoner Louis) (Slumerville (Pine Tree Road) 80)))
    (assert! (job (Reasoner Louis) (computer programmer trainee)))
    (assert! (salary (Reasoner Louis) 30000))
    (assert! (supervisor (Reasoner Louis) (Hacker Alyssa P)))
    (assert! (supervisor (Bitdiddle Ben) (Warbucks Oliver)))
    (assert! (address (Warbucks Oliver) (Swellesley (Top Heap Road))))
    (assert! (job (Warbucks Oliver) (administration big wheel)))
    (assert! (salary (Warbucks Oliver) 150000))
    (assert! (address (Scrooge Eben) (Weston (Shady Lane) 10)))
    (assert! (job (Scrooge Eben) (accounting chief accountant)))
    (assert! (salary (Scrooge Eben) 75000))
    (assert! (supervisor (Scrooge Eben) (Warbucks Oliver)))
    (assert! (address (Cratchet Robert) (Allston (N Harvard Street) 16)))
    (assert! (job (Cratchet Robert) (accounting scrivener)))
    (assert! (salary (Cratchet Robert) 18000))
    (assert! (supervisor (Cratchet Robert) (Scrooge Eben)))
    (assert! (address (Aull DeWitt) (Slumerville (Onion Square) 5)))
    (assert! (job (Aull DeWitt) (administration secretary)))
    (assert! (salary (Aull DeWitt) 25000))
    (assert! (supervisor (Aull DeWitt) (Warbucks Oliver)))
    (assert! (can-do-job (computer wizard) (computer programmer)))
    (assert! (can-do-job (computer wizard) (computer technician)))
    (assert! (can-do-job (computer programmer)
                         (computer programmer trainee)))
    (assert! (can-do-job (administration secretary)
                         (administration big wheel)))))

;;; Exercise 4.74

(defn simple-flatten
  [stream] (map first (filter (comp not empty?) stream)))

(defn simple-stream-flatmap
  [proc s] (simple-flatten (map proc s)))

;;; Exercise 4.75

(defn uniquely-asserted
  [[query & _] frames qeval]
  (->> frames
       (map #(qeval query (list %)))
       (filter #(= (count %) 1))
       (mapcat identity)))

(def qeval-special-forms-with-unique
  (assoc qeval-basic-special-forms
    :unique uniquely-asserted))

(def qeval-with-unique
  (make-qeval qeval-special-forms-with-unique))

;;; Exercise 4.76

(defn unify-frames
  [f1 f2]
  (loop [f1 (seq f1) f2 f2]
    (if (empty? f1)
      f2
      (let [[var val] (first f1)
            f2 (extend-if-possible var val f2)]
        (if (= f2 :failed)
          :failed
          (recur (rest f1) f2))))))

(defn intersect-frame-streams
  [s1 s2]
  (filter #(not= :failed %)
          (for [f1 s1 f2 s2] (unify-frames f1 f2))))

(defn qeval-conjoin-alt
  [conjuncts frames qeval]
  (loop [conjuncts conjuncts
         result frames]
    (if (empty? conjuncts)
      result
      (recur (rest conjuncts)
             (intersect-frame-streams
              result
              (qeval (first conjuncts) frames))))))

(def qeval-special-forms-with-alt-conjoin
  (assoc qeval-basic-special-forms
    :and qeval-conjoin-alt))

(def qeval-with-alt-conjoin
  (make-qeval qeval-special-forms-with-alt-conjoin))

;;; Exercise 4.77

;; The easiest and most intuitive way to solve this problem is to
;; reorder the clauses in `and` query, placing `not` and `lisp-value`
;; sub-queries at the end.

(defn reorder-conjoin-clauses
  [conjuncts]
  (let [{x false y true}
        (group-by #(let [op (first %)]
                     (or (= op 'lisp-value)
                         (= op 'not)))
                  conjuncts)]
    (concat x y)))

(defn qeval-conjoin-filter-fix
  [conjuncts frames qeval]
  (let [conjuncts (reorder-conjoin-clauses conjuncts)]
    (qeval-conjoin conjuncts frames qeval)))

(def qeval-special-forms-with-filter-fix
  (assoc qeval-basic-special-forms
    :and qeval-conjoin-filter-fix))

(def qeval-with-filter-fix
  (make-qeval qeval-special-forms-with-filter-fix))

