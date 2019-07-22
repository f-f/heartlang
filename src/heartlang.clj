(ns heartlang
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
            'let (let [[arg value] (second expr)
                       _ (assert (symbol? arg))]
                   {:op :let
                    :data {:sym (str arg)
                           :value (parse value)
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
(parse '(let [x 1]
          (let [y 2]
            (+ x y))))


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

(defn env-insert [env sym val]
  (cons [sym val] env))

(defn env-lookup [env sym]
  (when (seq env)
    (let [[sym-e v] (first env)]
      (if (= sym sym-e)
        v
        (recur (rest env) sym)))))

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
(defn typecheck [expr ctx]
  (condp = (:op expr)
    ;; 1. vars should be in context
    :var (if-let [typ (ctx-lookup ctx (-> expr :data :sym))]
           typ
           (throw (Exception. (str "Unbound variable " expr))))

    ;; 2. constants have a type
    :Natural {:op :Type}
    :nat     {:op :Natural}

    ;; 3. Lambda: if adding x : t1 to context gives e : t2, then the lambda has type x:t1 -> t2
    :lam (let [{:keys [sym typ body]} (:data expr)
               _ (typecheck typ ctx)
               new-ctx (ctx-insert ctx sym typ)
               body-type (typecheck body new-ctx)
               pi {:op :pi :data {:a typ :b body-type}}
               _ (typecheck pi ctx)]
           pi)

    ;; 3.5. Lambda types: type annotations must only contain types
    :pi (let [{:keys [a b]} (:data expr)
              a' (typecheck a ctx)
              b' (typecheck b ctx)]
          (if (and (= :Type (:op a'))
                   (= :Type (:op b')))
            {:op :Type}
            (throw (Exception. (str "Invalid input or output type: " a' b')))))

    ;; 4. Application: f : t1 -> t2 and a : t1 in the context, then (f a) : t2
    :app (let [{:keys [f a]} (:data expr)
               f-typ (typecheck f ctx)
               a-typ (typecheck a ctx)]
           (if (= :pi (:op f-typ))
             (if (= a-typ (-> f-typ :data :a))
               (-> f-typ :data :b)
               (throw (Exception. (str "Type mismatch: tried to apply function to the wrong type:\n\n" f-typ "\n\n" a-typ))))
             (throw (Exception. (str "Unsupported function type: " f-typ)))))


    ;; Extensions to the core STLC

    ;; let is just sugar for applied lambda
    :let (let [{:keys [sym value body]} (:data expr)
               lam {:op :lam
                    :data {:sym sym
                           :typ (typecheck value ctx)
                           :body body}}
               app {:op :app
                    :data {:f lam
                           :a value}}]
           (typecheck app ctx))

    ;; + is Natural -> Natural -> Natural
    :add (let [{:keys [a b]} (:data expr)
               a-typ (typecheck a ctx)
               b-typ (typecheck b ctx)]
           (if (or (not= :Natural (:op a-typ))
                   (not= :Natural (:op b-typ)))
             (throw (Exception. (str "Tried to apply + to wrong types: " a-typ b-typ)))
             {:op :Natural}))))



;; Testing typecheck

(defn check [expr]
  (-> expr
     parse
     (typecheck '())))

(check 42)
;; Typechecking works, no unbound variables allowed
;; (check 'x)
;; (check '(fn [x :- y] z))
(check '(fn [x :- Natural] x))

(check 'Natural)
;; + is a builtin so it's special and doesn't typecheck in isolation
;; (check '+)
(check '(+ 1 2))
(check '(fn [x :- Natural] (+ x 42))) ;; But we can apply it to things with no problem
(check '((fn [x :- Natural] (+ x 42)) 1))

;; This is not System F, as we don't have polymorphism
;; (check 'Type)
;; (check '(fn [x :- Type] (fn [y :- x] y)))  ;; <- Identity function

;; You can pass functions too!
(check '((fn [f :- (-> Natural Natural)]
           (f 42))
         (fn [x :- Natural] (+ x 1))))

;; Shadowing works correctly
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
(defn normalise [expr env]
  (condp = (:op expr)
    ;; Just replace a var with the value in the env
    :var (or (env-lookup env (-> expr :data :sym))
             expr)

    ;; Generate fresh names for all bindings
    :lam (let [{:keys [sym typ body]} (:data expr)
               new-sym (str (gensym))
               new-env (env-insert env sym {:op :var
                                            :data {:sym new-sym}})]
           {:op :lam
            :data {:sym new-sym
                   :typ (normalise typ env)
                   :body (normalise body new-env)}})

    ;; Apply lambdas: this is the actual equational operation
    :app (let [{:keys [f a]} (:data expr)
               f' (normalise f env)
               a' (normalise a env)]
           (if (= :lam (:op f'))
             ;; Normal case: we apply a lambda to a value
             (let [{:keys [sym typ body]} (:data f')
                   new-env (env-insert env sym a')]
               (normalise body new-env))
             ;; Otherwise we just normalise the bodies
             {:op :app
              :data {:f f'
                     :a a'}}))

    ;; Extensions

    :add (let [{:keys [a b]} (:data expr)
               a' (normalise a env)
               b' (normalise b env)]
           (if (and (= :nat (:op a'))
                    (= :nat (:op b')))
             {:op :nat
              :data {:n (+ (-> a' :data :n)
                           (-> b' :data :n))}}
             {:op :add
              :data {:a a'
                     :b b'}}))

    :let (let [{:keys [sym value body]} (:data expr)
               lam {:op :lam
                    :data {:sym sym
                           :typ (normalise value env)
                           :body body}}
               app {:op :app
                    :data {:f lam
                           :a value}}]
           (normalise app env))

    ;; Constants just fall through
    expr))



;; Test normalisation

(defn run [expr]
  (let [e (parse expr)
        _ (typecheck e '())]
    ;; (println "")
    (-> (normalise e '())
       pretty
       )))
       ;; clojure.pprint/pprint)))


(run 42)
(run '(fn [x :- Natural] x))
(run '((fn [x :- Natural] x) 42))

(run '((fn [y :- Natural]
         ((fn [x :- Natural] x)
          y))
       42))

(run 'Natural)

;; (run 'Type)
;; (run 'x)
;; (run '(fn [x :- y] z))
;; (run '+)

(run '(+ 1 2))
(run '(fn [x :- Natural]
        (+ x 42)))
(run '((fn [x :- Natural]
         (+ x 42))
       1))

(run '(fn [x :- Natural]
        (fn [y :- Natural]
          (fn [z :- Natural]
            (+ y z)))))

(run '(let [x 1]
        x))

;; Shadowing
(run '((fn [x :- Natural]
         ((fn [x :- Natural] x)
          17))
       42))

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
