(ns heartlang.core
  (:gen-class))


;;

(def help
  "

Heartlang is a single-file implementation of Simply Typed Lambda Calculus,
with Naturals and LISP syntax

Syntax:
- Naturals:      42
- Symbols:       x
- Constants:     Type
                 Natural
- Lambdas:       (fn [argument :- type] body)
- Function type: (-> Type Type)
??? - Let:           (let [name definition] body)
- Addition:      (+ e1 e2)
- Application:   (some-function argument)


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
                      _ (assert (= (str col) ":-"))
                      _ (assert (symbol? arg))]
                 {:op :lam
                  :data {:sym (str arg)
                         :typ (parse' typ)
                         :body (parse' (nth expr 2))}})
            ;; 'let?
            ;;'+ {:op :add
            ;;    :data {:a (parse' (nth expr 1))
            ;;           :b (parse' (nth expr 2))}}
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
                               :a (parse' (first more))}}))))))
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
    :add     {:op :pi
              :data {:a {:op :Natural}
                     :b {:op :pi
                         :data {:a {:op :Natural}
                                :b {:op :Natural}}}}}

    ;; 3. Lambda: if adding x : t1 to context gives e : t2, then the lambda has type x:t1 -> t2
    :lam (let [{:keys [sym typ body]} (:data expr)
               _ (typecheck typ env ctx)
               normal-typ typ ;;  (normalise typ) ;;; ??????
               new-ctx (ctx-insert ctx sym normal-typ)
               body-type (typecheck body env new-ctx)]
               ;; Maybe pi?
           {:op :pi :data {:a normal-typ :b body-type}})

    ;; How about PI?

    ;; 4. Application: f : t1 -> t2 and a : t1 in the context, then (f a) : t2
    :app (let [{:keys [f a]} (:data expr)
               f-typ (typecheck f env ctx)
               a-typ (typecheck a env ctx)]
           (if (= :pi (:op f-typ))
             (if (= a-typ (-> f-typ :data :a))
               (-> f-typ :data :b)
               (throw (Exception. (str "Type mismatch: tried to apply function to the wrong type:\n\n" f-typ "\n\n" a-typ))))
             (throw (Exception. (str "Unsupported function type: " f-typ)))))))


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

;; Shadowing
(check ((fn [x :- Natural] ((fn [x :- Type] x) Natural)) 42))

;; Pi?
(check ((fn [f :- (-> Natural Natural)]
          (f 42))
        (fn [x :- Natural] (+ x 1))))


;; Normalisation

(defn normalise [expr env]
  (condp = (:op expr)
    :var (or (env-lookup env (-> expr :data :sym))
             expr)

    :lam (let [{:keys [sym typ body]} (:data expr)
               new-sym (str (gensym))
               new-env (env-insert env sym {:op :var
                                            :data {:sym new-sym}})]
           {:op :lam
            :data {:sym new-sym
                   :typ (normalise typ env)
                   :body (normalise body new-env)}})

    :app (let [{:keys [f a]} (:data expr)
               f' (normalise f env)
               a' (normalise a env)]
           (if (= :lam (:op f'))
             ;; Normal case: we apply a lambda to a value
             (let [{:keys [sym typ body]} (:data f')
                   new-env (env-insert env sym a')]
               (normalise body new-env))
             ;; Builtins case
             (if (and ))
             {:op :app
              :data {:f f'
                     :a a'}}))

    ;; Constants just fall through
    expr))



;; Test normalisation

(defmacro run [expr]
  (let [e (parse' expr)
        _ (typecheck e '() '())]
    (normalise e '())))

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
(run (fn [x :- Natural] (+ x 42)))
(run ((fn [x :- Natural] (+ x 42)) 1))

;; Shadowing
(run ((fn [x :- Natural] ((fn [x :- Type] x) Natural)) 42))








;; Bonus: pretty











(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!"))
