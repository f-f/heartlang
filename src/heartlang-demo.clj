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
- Let:           (let [name definition] body)
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
(defn parse [expr])








;; Testing parsing



















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

(defn typecheck [expr ctx])











;; Testing typecheck

(defn check [expr]
  (-> expr
     parse
     (typecheck '())))




















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
