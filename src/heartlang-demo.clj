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


    ;; 2. constants have a type


    ;; 3. Lambda: if adding x : S to context gives e : T,
    ;; then the lambda has type S -> T


    ;; 3.5 Lambda types: type annotations must only contain types


    ;; 4. Application: if f : S -> T and a : S are in context
    ;; then (f a) : T


    ;; Extension: Naturals

    ))
















;; Testing typecheck

(defn check [expr]
  (-> expr
     parse
     (typecheck '())))


(check 42)

;; No unbound variables allowed
;; (check 'x)
;; (check '(fn [x :- y] z))

(check '(fn [x :- Natural] x))


(check 'Natural)

(check '(+ 1 2))
(check '(fn [x :- Natural] (+ x 42)))
(check '((fn [x :- Natural] (+ x 42)) 1))

;; You can pass functions too!
(check '((fn [f :- (-> Natural Natural)]
           (f 42))
         (fn [x :- Natural] (+ x 1))))

;; Shadowing works properly
(check '((fn [x :- (-> Natural Natural)]
           ((fn [x :- Natural] x)
            42))
         (fn [x :- Natural] x)))



















;; Normalisation
;;
;; This is the "evaluation" of Lambda Calculus, where "abstraction"
;; (i.e. function definitions) are applied to values.
;;
;; The actual work happens when handling `app` nodes, everything
;; else is kind of accessory work (to prevent name collisions, etc.)
;;
(defn normalise [expr env])
















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
