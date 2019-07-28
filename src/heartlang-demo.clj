(ns heartlang-demo
  (:require
   [clojure.pprint]
   [clojure.edn])
  (:gen-class))





(def help
  "

Heartlang is a single-file implementation of Simply Typed Lambda Calculus,
with Naturals and Clojur-ish syntax

Syntax:
- Naturals:      42
- Symbols:       x
- Types:         Natural
- Function type: (-> Natural Natural)
- Lambdas:       (fn [argument :- type] body)
- Application:   (some-function argument)
- Addition:      (+ e1 e2)

")













;; Stage warning
;;
;; Many things here are going to be very primitive because we are
;; lacking on time, but you can make them as good as you want.
;; For examples, errors are really bad, but they could be nice and
;; clear, especially if the implementation has type inference.







;; "Parsing"
;;
;; Here we skip all the fancy parser stuff and just use lispy syntax
;; (and a Clojure-compatible subset of it, e.g. we have to use `:-`
;; for type annotations) to get AST by walking the tree.
;;
(defn parse [expr]
  (condp #(%1 %2) expr
    nat-int? {:op :nat
              :data {:n expr}}
    symbol? (condp = expr
              'Natural {:op :Natural}
              '+ {:op :add}
              {:op :var
               :data {:sym (str expr)}})
    list? (condp = (first expr)
            'fn (let [[arg col typ] (second expr)
                     _ (assert (= col :-))
                     _ (assert (symbol? arg))]
                 {:op :lam
                  :data {:sym (str arg)
                         :typ (parse typ)
                         :body (parse (nth expr 2))}})
            '+ {:op :add
                :data {:a (parse (nth expr 1))
                       :b (parse (nth expr 2))}}
            '-> {:op :pi
                :data {:a (parse (nth expr 1))
                       :b (parse (nth expr 2))}}
            (loop [more (nnext expr)
                   app {:op :app
                        :data {:f (parse (first expr))
                               :a (parse (second expr))}}]
              (if-not (seq more)
                app
                (recur (rest more)
                       {:op :app
                        :data {:f app
                               :a (parse (first more))}}))))
    (str "ERROR: wasn't able to parse: " expr)))








;; Testing parsing

(parse 42)

(parse 'x)

(parse 'Natural)

(parse '(fn [x :- y] z))

(parse '(+ x 42))

(parse '(fn [x :- Natural] (+ x 42)))

(parse '((fn [f :- (-> Natural Natural)]
           (f 42))
         (fn [x :- Natural] (+ x 1))))













;; Bonus section: pretty printing
;;
;;  This just takes an expression and renders it so that if you
;;  pass it through `clojure.edn/read` and `parse` it back you'd
;;  get the original expression
;;
(defn pretty [expr]
  (condp = (:op expr)
    :var (-> expr :data :sym symbol)
    :Type 'Type
    :Natural 'Natural
    :nat (-> expr :data :n)
    :lam (let [{:keys [sym typ body]} (:data expr)]
           (list 'fn [(symbol sym) :- (pretty typ)] (pretty body)))
    :app (let [{:keys [f a]} (:data expr)]
           (list (pretty f) (pretty a)))
    :add (let [{:keys [a b]} (:data expr)]
           (list '+ (pretty a) (pretty b)))
    :pi (let [{:keys [a b]} (:data expr)]
          (list '-> (pretty a) (pretty b)))))



(-> '(+ x 42) parse)

(-> '(+ x 42) parse pretty)











;; Towards typechecking
;;
;; When typechecking and evaluating a program, it is necessary to
;; keep track of what has been evaluated before and bound to various
;; symbols. We call that "context" when typechecking, and "environment"
;; when evaluating.
;; Here they are both going to have the same implementation - a list to
;; which we `cons` fresh names when we encounter new bindings - but they
;; have different semantics:
;; - `ctx` binds names to types
;; - `env` binds names to values

(defn env-insert [env sym val]
  (cons [sym val] env))

(defn env-lookup [env sym]
  (-> env (filter (fn [[sym-e v]] (= sym-e sym))) first second))

(def ctx-lookup env-lookup)
(def ctx-insert env-insert)

















;; Typecheck
;;
;; We implement Simply Typed Lambda Calculus:
;; https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus
;;
;; This means that we have a simple typesystem, that basically only
;; adds type matching for lambda binders over untyped LC.
;; See the above link or the slides for the four typing rules
;; mentioned in comments below.
;;

(defn throw-unbound [expr]
  (throw (Exception. (str "Unbound variable: " expr))))
(defn throw-invalid-pi [a b]
  (throw (Exception. (str "Invalid in or out type: " a b))))
(defn throw-type-app-mismatch [f a]
  (throw (Exception. (str "Tried to apply fn to wrong type: " f a))))
(defn throw-type-plus-mismatch [a b]
  (throw (Exception. (str "Tried to apply + to wrong types: " a b))))
(defn throw-wrong-fn-type [f]
  (throw (Exception. (str "Unsupported function type: " f))))




(defn typecheck [expr ctx]
  (condp = (:op expr)

    ;; 1. vars should be in context
    ;;
    ;; {:op :var :data {:sym "x"}}
    ;;
    :var "TODO"


    ;; 2. constants have a type
    ;;
    ;; {:op :nat :data {:n 42}}
    ;; {:op :Natural}
    ;;
    :nat "TODO"
    :Natural "TODO"


    ;; 3. Lambda: if adding x : S to context gives e : T,
    ;; then the lambda has type S -> T
    ;;
    ;; {:op :lam
    ;;  :data {:sym "x"
    ;;         :typ {:op :Natural}
    ;;         :body {:op :var :data {:sym "x"}}}}
    ;;
    :lam (let [{:keys [sym typ body]} (:data expr)]
           "TODO")


    ;; 3.5 Lambda types: type annotations must only contain types
    ;;
    ;; {:op :pi :data {:a {:op :Natural} :b {:op :Natural}}}
    ;;
    :pi (let [{:keys [a b]} (:data expr)]
          "TODO")


    ;; 4. Application: if f : S -> T and a : S are in context
    ;; then (f a) : T
    ;;
    ;; {:op :app
    ;;  :data {:f {:op :lam
    ;;             :data {:sym "x"
    ;;                    :typ {:op :Natural}
    ;;                    :body {:op :var :data {:sym "x"}}}}
    ;;         :a {:op :nat :data {:n 42}}}}
    ;;
    :app (let [{:keys [f a]} (:data expr)]
           "TODO")


    ;; Extension: Natural addition
    ;;
    ;; {:op :add
    ;;  :data {:a {:op :nat :data {:n 42}}
    ;;         :b {:op :nat :data {:n 17}}}}
    ;;
    :add (let [{:keys [a b]} (:data expr)]
           "TODO")

    ))
















;; Testing typecheck

(defn check [expr]
  (-> expr
     parse
     (typecheck '())))


(check 42)

;; No unbound variables allowed
;;(check 'x)
;;(check '(fn [x :- y] z))

(check '(fn [x :- Natural] x))


(check 'Natural)

(check '(+ 1 2))
(check '(fn [x :- Natural] (+ x 42)))
(check '((fn [x :- Natural] (+ x 42)) 1))

;; You can pass functions too!
(check '((fn [f :- (-> Natural Natural)]
           (f 42))
         (fn [x :- Natural] (+ x 1))))

















;; Normalisation
;;
;; This is the "evaluation" of Lambda Calculus, where "abstraction"
;; (i.e. function definitions) are applied to values.
;;
;; The actual work happens when handling `app` nodes, everything
;; else is kind of accessory work (to prevent name collisions, etc.)
;;
(defn normalise [expr env]
  (condp = (:op expr)
    ;; Just replace a var with the value in the env
    :var (or (env-lookup env (-> expr :data :sym))
             expr)

    ;; Generate fresh names for all bindings
    :lam (let [{:keys [sym typ body]} (:data expr)
               new-sym (str (gensym))
               new-env (env-insert env sym {:op :var :data {:sym new-sym}})]
           {:op :lam
            :data {:sym new-sym
                   :typ (normalise typ env)
                   :body (normalise body new-env)}})



    ;; Apply lambdas: this is the actual application of beta-normalization
    :app (let [{:keys [f a]} (:data expr)]
           "TODO")


    ;; Extension: natural addition
    :add (let [{:keys [a b]} (:data expr)
               a' (normalise a env)
               b' (normalise b env)]
           (if (and (= :nat (:op a'))
                    (= :nat (:op b')))
             {:op :nat :data {:n (+ (-> a' :data :n) (-> b' :data :n))}}
             {:op :add :data {:a a' :b b'}}))

    ;; Fallback case
    expr
    ))
















;; Test normalisation

(defn run [expr]
  (let [e (parse expr)
        _ (typecheck e '())]
    (-> (normalise e '())
       pretty)))



(run 42)

(run '(fn [x :- Natural] x))

;; But what if we apply the function?
(run '((fn [x :- Natural] x) 42))


(run 'Natural)


(run '(+ 1 2))

(run '(fn [x :- Natural]
        (+ x 42)))

(run '((fn [x :- Natural]
         (+ x 42))
       1))

;; Nested functions carry on the environments properly
(run '(fn [x :- Natural]
        (fn [y :- Natural]
          (fn [z :- Natural]
            (+ y z)))))

;; Shadowing evaluates nicely
(run '((fn [x :- Natural]
         ((fn [x :- Natural] x)
          17))
       42))

;; Passing in functions works too
(run '((fn [f :- (-> Natural Natural)]
         (f 42))
       (fn [x :- Natural] (+ x 1))))























;; Bonus section: run programs from stdin
;;
;;  If you have the `clj` tool you can just put this file in a `src`
;;  folder and evaluate Heartlang expressions from the terminal like so:
;;
;;  $ clj -m heartlang <<< "(let [x 23] (let [y 19] (+ x y)))"
;;
;;  => 42
;;
(defn -main [& args]
  (let [in (slurp *in*)
        expr (clojure.edn/read
              (java.io.PushbackReader.
               (clojure.java.io/reader
                (.getBytes in))))
        expr (parse expr)
        _ (typecheck expr '())]
    (-> (normalise expr '())
        pretty
        clojure.pprint/pprint)))
