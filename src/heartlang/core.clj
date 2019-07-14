(ns heartlang.core
  (:gen-class))

(def help
  "

Heartlang is a single-file implementation of Simply Typed Lambda Calculus,
with Naturals and Clojur-ish syntax

Syntax:
- Naturals:      42
- Symbols:       x
- Constants:     Type
                 Natural
- Lambdas:       (fn [argument :- type] body)
- Function type: (-> Type Type)
- Application:   (some-function argument)
- Let:           (let [name definition] body)
- Addition:      (+ e1 e2)

")


(defn parse' [expr]
  (condp #(%1 %2) expr
    nat-int? {:op :nat
              :data {:n expr}}
    symbol? (condp = expr
              'Type {:op :Type}
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
                         :typ (parse' typ)
                         :body (parse' (nth expr 2))}})
            'let (let [[arg value] (second expr)
                       _ (assert (symbol? arg))]
                   {:op :let
                    :data {:sym (str arg)
                           :value (parse' value)
                           :body (parse' (nth expr 2))}})
            '+ {:op :add
                :data {:a (parse' (nth expr 1))
                       :b (parse' (nth expr 2))}}
            '-> {:op :pi
                 :data {:a (parse' (nth expr 1))
                        :b (parse' (nth expr 2))}}
            (loop [more (nnext expr)
                   app {:op :app
                        :data {:f (parse' (first expr))
                               :a (parse' (second expr))}}]
              (if-not (seq more)
                app
                (recur (rest more)
                       {:op :app
                        :data {:f app
                               :a (parse' (first more))}}))))
    (str "ERROR: wasn't able to parse: " expr)))

(defmacro parse [expr]
  (parse' expr))


;; Testing parsing

(parse 42)
(parse x)
(parse Type)
(parse Natural)
(parse (fn [x :- y] z))
(parse (+ x 42))
(parse (fn [x :- Natural] (+ x 42)))
(parse ((fn [f :- (-> Natural Natural)]
          (f 42))
        (fn [x :- Natural] (+ x 1))))
(parse (let [x 1]
         (let [y 2]
           (+ x y))))


;; Typecheck

;; ctx is container for types
;; env is container for values


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

(declare normalise)

(defn typecheck [expr env ctx]
  (condp = (:op expr)
    ;; 1. vars should be in context
    :var (if-let [typ (ctx-lookup ctx (-> expr :data :sym))]
           typ
           (throw (Exception. (str "Unbound variable " expr ctx env))))

    ;; 2. constants have a type
    :Type    {:op :Type}
    :Natural {:op :Type}
    :nat     {:op :Natural}

    ;; 3. Lambda: if adding x : t1 to context gives e : t2, then the lambda has type x:t1 -> t2
    :lam (let [{:keys [sym typ body]} (:data expr)
               _ (typecheck typ env ctx)
               normal-typ typ ;;  (normalise typ) ;;; ??????
               new-ctx (ctx-insert ctx sym normal-typ)
               body-type (typecheck body env new-ctx)]
               ;; Maybe pi?
           {:op :pi :data {:a normal-typ :b body-type}})

    ;; 4. Application: f : t1 -> t2 and a : t1 in the context, then (f a) : t2
    :app (let [{:keys [f a]} (:data expr)
               f-typ (typecheck f env ctx)
               a-typ (typecheck a env ctx)]
           (if (= :pi (:op f-typ))
             (if (= a-typ (-> f-typ :data :a))
               (-> f-typ :data :b)
               (throw (Exception. (str "Type mismatch: tried to apply function to the wrong type:\n\n" f-typ "\n\n" a-typ))))
             (throw (Exception. (str "Unsupported function type: " f-typ)))))

    ;; Extensions


    ;; How about pi?

    ;; let is just sugar for a lambda
    :let (let [{:keys [arg value body]} (:data expr)]
           (typecheck  env ctx))

    ;; + is Natural -> Natural -> Natural
    :add (let [{:keys [a b]} (:data expr)
               a-typ (typecheck a env ctx)
               b-typ (typecheck b env ctx)]
           (if (or (not= :Natural (:op a-typ))
                   (not= :Natural (:op b-typ)))
             (throw (Exception. (str "Tried to apply + to wrong types: " a-typ b-typ)))
             {:op :Natural}))))



;; Testing typecheck

(defmacro check [expr]
  (typecheck (parse' expr) '() '()))

(check 42)
(check x)
(check (fn [x :- Natural] x))
(check Type)
(check Natural)
(check (fn [x :- y] z))
(check +)
(check (+ 1 2))
(check (fn [x :- Natural] (+ x 42)))
(check ((fn [x :- Natural] (+ x 42)) 1))

;; Oops, accidentally implemented System F
(check (fn [x :- Type] (fn [y :- x] y)))

;; Shadowing
(check ((fn [x :- Natural] ((fn [x :- Type] x) Natural)) 42))

;; Pi?
(check ((fn [f :- (-> Natural Natural)]
          (f 42))
        (fn [x :- Natural] (+ x 1))))


;; Normalisation

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

    ;; Extensions: natural addition
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

    ;; Constants just fall through
    expr))



;; Test normalisation

(defmacro run [expr]
  (let [e (parse' expr)
        _ (typecheck e '() '())]
    (println "")
    (-> (normalise e '())
       pretty
       clojure.pprint/pprint)))


(run 42)
(run x)
(run (fn [x :- Natural] x))
(run ((fn [x :- Natural] x) 42))

(run ((fn [y :- Natural]
        ((fn [x :- Natural] x)
         y))
      42))

(run Type)
(run Natural)
(run (fn [x :- y] z))
(run +)
(run (+ 1 2))
(run (fn [x :- Natural]
       (+ x 42)))
(run ((fn [x :- Natural]
        (+ x 42))
      1))

(run (fn [x :- Natural] (fn [y :- Natural] (fn [z :- Natural] (+ y z)))))

;; Shadowing
(run ((fn [x :- Natural]
        ((fn [x :- Type] x)
         Natural))
      42))








;; Bonus: pretty

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









(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!"))
