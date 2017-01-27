(ns clojure-sicp.chapter3)

;;; Exercise 3.1

(defn make-accumulator
  [starting-value]
  (let [initial (atom starting-value)]
    (fn [additional] (swap! initial (partial + additional)))))

;;; Exercise 3.2

(defn make-monitored
  [f]
  (let [num-calls (atom 0)]
    (fn [x]
      (cond (= x 'how-many-calls?) @num-calls
            (= x 'reset-calls) (swap! num-calls (fn [x] 0))
            :else (do
                    (swap! num-calls inc)
                    (f x))))))

;;; Exercise 3.3

(defn make-account
  [starting-balance password]
  (let [balance (atom starting-balance)]
    (letfn [(withdraw [amount]
              (if (>= @balance amount)
                (do (swap! balance #(- % amount))
                    @balance)
                "insufficient funds"))
            (deposit [amount]
              (swap! balance #(+ % amount))
              @balance)
            (dispatch [supplied-pw action]
              (if (= supplied-pw password)
                (cond (= action 'withdraw) withdraw
                      (= action 'deposit) deposit
                      :else (Error. (str "Unknown request -- MAKE-ACCOUNT " action)))
                (fn [x] "incorrect password")))]
      dispatch)))

;;; Exercise 3.4

(defn make-account
  [starting-balance password]
  (let [balance (atom starting-balance)
        attempts (atom 0)]
    (letfn [(withdraw [amount]
              (if (>= @balance amount)
                (do (swap! balance #(- % amount))
                    @balance)
                "insufficient funds"))
            (deposit [amount]
              (swap! balance #(+ % amount))
              @balance)
            (dispatch [supplied-pw action]
              (if (= supplied-pw password)
                (do
                  (swap! attempts (fn [x] 0))
                  (cond (= action 'withdraw) withdraw
                        (= action 'deposit) deposit
                        :else (Error. (str "Unknown request - make-account " action))))
                (do
                  (swap! attempts inc)
                  (if (> @attempts 7)
                    (fn [x] "Weeeu-weeeu")
                    (fn [x] "incorrect password")))))]
      dispatch)))

;;; Exercise 3.5

(defn monte-carlo
  [trials experiment]
  (loop [trials-remaining trials
         trials-passed 0]
    (cond (= trials-remaining 0) (/ trials-passed trials)
          (experiment) (recur (dec trials-remaining) (inc trials-passed))
          :else (recur (dec trials-remaining) trials-passed))))

(defn random-in-range
  [low high]
  (+ low (rand (- high low))))

(defn rectangle-area
  [x1 x2 y1 y2]
  (Math/abs (* (- x2 x1) (- y2 y1))))

(defn estimate-integral
  [p x1 x2 y1 y2 trials]
  (letfn
      [(experiment []
         (let [x (random-in-range x1 x2)
               y (random-in-range y1 y2)]
           (p x y)))]
    (* (rectangle-area x1 x2 y1 y2)
       (monte-carlo trials experiment))))

(defn square
  [x]
  (Math/pow x 2))

(defn estimate-pi-using-area-unit-circle
  []
  (letfn [(unit-circle-predicate [x y]
            (<= (+ (square x) (square y)) 1))]
    (double
     (estimate-integral
      unit-circle-predicate -1.0 1.0 -1.0 1.0 10000))))

;;; Exercise 3.6

(defn rand-update
  [x]
  (let [a 5.2 b 3.1 m 1.5]
    (mod (+ (* a x) b) m)))

(def my-rand
  (let [current-random (atom 5.0)]
    (fn
      ([]
       (swap! current-random rand-update)
       @current-random)
      ([action]
       (if (= action :generate) (my-rand)))
      ([action seed]
       (if (= action :reset) (swap! current-random (fn [x] seed)))))))

;;; Exercise 3.7

(defn make-account
  [starting-balance password]
  (let [balance (atom starting-balance)]
    (letfn [(withdraw [amount]
              (if (>= @balance amount)
                (do (swap! balance #(- % amount))
                    @balance)
                "insufficient funds"))
            (deposit [amount]
              (swap! balance #(+ % amount))
              @balance)
            (dispatch [supplied-pw action]
              (if (= supplied-pw password)
                (cond (= action 'withdraw) withdraw
                      (= action 'deposit) deposit
                      :else (Error. (str "Unknown request -- MAKE-ACCOUNT " action)))
                (fn [x] "incorrect password")))]
      dispatch)))

(defn make-joint
  [account owners-pw joint-pw]
  (fn [password action]
    (if (= joint-pw password) (account owners-pw action)
        (Error. (str "BAD PASSWORD -- " password)))))

;;; Exercise 3.8

(def f
  (let [state (atom 0)]
    (letfn [(switch-state [x]
      (let [old-state @state]
        (reset! state (+ x old-state))
        old-state))]
      switch-state)))

;;; Exercise 3.17

(defn car
  [p]
  (:car @p))

(defn cdr
  [p]
  (:cdr @p))

(defn has?
  [x es]
  (some #(= % x) es))

(defn atom? [x]
  (= clojure.lang.Atom (type x)))

(defn count-pairs
  [x]
  (let [visited (atom '())
        iter (fn iter [s]
               (cond (not (atom? s)) 0
                     (has? s @visited) 0
                     :else (do
                             (swap! visited #(cons s %))
                             (+ 1
                                (iter (cdr s))
                                (iter (car s))))))]
    (iter x)))

;;; Exercise 3.18

(defn cycles?
  [s]
  (loop [curr s, visited '()]
    (cond (has? curr visited) true
          (= nil (cdr curr)) false
          :else (recur
                 (cdr curr)
                 (cons curr visited)))))

;;; Exercise 3.19

(defn cycles?
  [s]
  (loop [one s two (cdr s)]
    (cond (= one two) true
          (or (= nil one) (= nil two)) false
          (= nil (cdr two)) false
          :else (recur (cdr one) (cdr (cdr two))))))

;;; Exercise 3.22

(defstruct pair :car :cdr)

(defn set-car!
  [p x]
  (swap! p #(assoc % :car x)))

(defn set-cdr!
  [p x]
  (swap! p #(assoc % :cdr x)))

(defn pair?
  [p]
  (and (= clojure.lang.Atom (type p))))

(defn make-pair
  ([] (make-pair nil nil))
  ([a] (make-pair a nil))
  ([a b] (atom (struct pair a b))))

(defn make-queue
  []
 (let [front-ptr (atom :empty)
       rear-ptr (atom :empty)]
  (letfn [(set-front-ptr! [x] (swap! front-ptr (fn [y] x)))
          (set-rear-ptr! [x] (swap! rear-ptr (fn [y] x)))
          (set-front-and-rear-ptr! [x]
           (set-front-ptr! x)
           (set-rear-ptr! x))
          (empty-queue? []
           (and (= :empty @front-ptr) (= :empty @rear-ptr)))
          (front []
           (if (empty-queue?) (Error. "FRONT called for empty queue")
               (car @front-ptr)))
          (insert! [x]
           (let [e (make-pair x)]
            (if (empty-queue?)
                (do (set-front-and-rear-ptr! e) dispatch)
                (do (set-cdr! @rear-ptr e)
                    (set-rear-ptr! e)
                    dispatch))))
          (delete! []
           (if (empty-queue?)
               (Error. "DELETE! called for empty queue")
               (if (= @front-ptr @rear-ptr)
                   (do (set-front-and-rear-ptr! :empty) dispatch)
                   (do (set-front-ptr! (cdr @front-ptr)) dispatch))))
          (dispatch
           ([action]
            (cond (= action :front) (front)
                  (= action :delete!) (delete!)
                  (= action :empty?) (empty-queue?)
                  :else (Error. (str action "is not supported"))))
           ([action e]
            (cond (= action :insert!) (insert! e)
                  :else (Error. (str action "is not supported")))))]
    dispatch)))

;;; Exercise 3.24

(defn my-cons
  [p1 p2]
  (make-pair
   (car p1)
   p2))

(defn my-list
  [& elems]
  (loop [xs (next (reverse elems))
         res (make-pair (first (reverse elems)))]
    (if (nil? xs) res
        (recur (next xs)
               (my-cons (make-pair (first xs))
                        res)))))

(defn make-table
  ([] (make-table =))
  ([same-key?]
      (let [local-table (my-list :*table*)]
        (letfn [
                (my-assoc [key1 records]
                  (cond (nil? records) false
                        (same-key? key1 (car (car records))) (car records)
                        :else (my-assoc key1 (cdr records))))
                (lookup [& kys]
                  (let [subtable (my-assoc (first kys) (cdr local-table))]
                    (lookup-internal (next kys) subtable)))
                (lookup-internal [kys cur]
                  (cond (and kys cur)
                          (let [rec (my-assoc (first kys) (cdr cur))]
                            (lookup-internal (next kys) rec))
                        (and (nil? kys) cur) (cdr cur)
                        (not cur) false))
                (insert! [key-1 key-2 value]
                  (let [subtable (my-assoc key-1 (cdr local-table))]
                    (if subtable
                        (let [record (my-assoc key-2 (cdr subtable))]
                          (if record
                              (set-cdr! record value)
                              (set-cdr! subtable
                                        (make-pair (make-pair key-2 value)
                                                   (cdr subtable)))))
                        (set-cdr! local-table
                                  (make-pair (my-list key-1
                                                      (make-pair key-2 value))
                                             (cdr local-table)))))
                  :ok)
                (dispatch [m]
                  (cond (= m :lookup-proc) lookup
                        (= m :insert-proc!) insert!
                        (= m :table) local-table
                        :else (Error. "Unknown operation - TABLE" m)))]
          dispatch))))

;;; Exercise 3.25

(defn make-table
  []
  (let [local-table (make-table)]
    (letfn [(lookup [kees] ((local-table :lookup-proc) kees :fizz))
            (insert [kees value] ((local-table :insert-proc!) kees :fizz value))]
      (fn [m]
        (cond (= m :lookup-proc) lookup
              (= m :insert-proc!) insert
              :else (Error. "Unknown operation - TABLE" m))))))

;;; Exercise 3.29

(def inverter-delay 2)
(def and-gate-delay 3)
(def or-gate-delay 5)

(defn call-each
  [procedures]
  (when procedures
    ((first procedures))
    (recur (next procedures))))

(defn logical-not
  [s]
  (cond (= s 0)	1
        (= s 1) 0
        :else (Error. "Invalid signal")))

(defn logical-and
  [a b]
  (cond (and (= a 1) (= b 1)) 1
        :else 0))

(defn get-signal
  [wire]
  (wire :get-signal))

(defn set-signal!
  [wire new-value]
  ((wire :set-signal!) new-value))

(defn add-action!
  [wire action-proc]
  ((wire :add-action!) action-proc))

(defn segments
  [agenda]
  (:items @agenda))

(defn make-time-segment
  [time action]
  {:time time :action action})

(defn set-segments!
  [agenda segments]
  (swap! agenda #(assoc % :items segments)))

(defn current-time
  [agenda]
  (:cur-time @agenda))

(defn add-to-agenda!
  [time action agenda]
  (letfn [(add-to-segments
            ([segments]
             (let [item (make-time-segment time action)]
               (sort-by :time (cons item segments)))))]
    (set-segments! agenda
                   (add-to-segments (segments agenda)))))

(defn after-delay
  [delay action]
  (let [the-agenda (atom {:cur-time 0 :items '()})]
    (add-to-agenda! (+ delay (current-time the-agenda))
                    action
                    the-agenda)))

(defn inverter
  [input output]
  (letfn [(invert-input
            []
            (let [new-value (logical-not (get-signal input))]
              (after-delay inverter-delay
                           (fn []
                             (set-signal! output new-value)))))]
    (add-action! input invert-input)))

(defn make-wire
  []
  (let [signal-value (atom 0)
        action-procedures (atom '())]
    (letfn [(set-my-signal!
              [new-value]
              (while (not (= new-value @signal-value))
                (swap! signal-value (fn [x] new-value))
                (call-each @action-procedures)))

            (accept-action-procedure!
              [proc]
              (swap! action-procedures #(cons proc %))
              (proc))
            (dispatch
              [m]
              (cond (= m :get-signal) @signal-value
                    (= m :set-signal!) set-my-signal!
                    (= m :add-action!) accept-action-procedure!
                    :else (Error. "Unkown operation -- WIRE" m)))]
      dispatch)))

(defn and-gate
  [a1 a2 output]
  (letfn [(and-action-procedure
            []
            (let [new-value
                  (logical-and (get-signal a1)
                               (get-signal a2))]
              (after-delay and-gate-delay
                           (fn []
                             (set-signal! output new-value)))))]
    (add-action! a1 and-action-procedure)
    (add-action! a2 and-action-procedure)))

(defn or-gate
  [a1 a2 output]
  (let [a (make-wire)
        b (make-wire)
        c (make-wire)]
    (inverter a1 a)
    (inverter a2 b)
    (and-gate a b c)
    (inverter c output))
  :ok)

;;; Exercise 3.30

(defn sandwich-list
  [start middle end]
  (reverse
   (list* end
          (reverse (list* start middle)))))

(defn make-wires
  [n]
  (for [x (range n)]
    (make-wire)))

(defn half-adder
  [a b s c]
  (let [d (make-wire), e (make-wire)]
    (or-gate a b d)
    (and-gate a b c)
    (inverter c e)
    (and-gate d e s)
    :ok))

(defn full-adder [a b c-in sum c-out]
  (let [s (make-wire)
        c1 (make-wire)
        c2 (make-wire)]
    (half-adder b c-in s c1)
    (half-adder a s sum c2)
    (or-gate c1 c2 c-out)
    :ok))

(defn ripple-carry-adder
  [As Bs Ss C]
  (let [n (count As)
        Cs (sandwich-list C (make-wires (- n 1)) 0)]
    (loop [as As, bs Bs, cs Cs, ss Ss]
      (if (nil? as) :ok)
      (full-adder (first as)
                  (first bs)
                  (second cs)
                  (first ss)
                  (first cs))
      (recur (next as)
             (next bs)
             (next cs)
             (next ss)))))

;;; Exercise 3.33

(defprotocol Constraint
  (process-new-value [this])
  (process-forget-value [this]))

(defprotocol Connection
  (has-value? [connection])
  (get-value [connection])
  (set-value! [connection new-value setter])
  (forget-value! [connection retractor])
  (connect [connection new-constraint]))

(defn inform-about-value
  [constraint]
  (process-new-value constraint))

(defn inform-about-no-value
  [constraint]
  (process-forget-value constraint))

(defn for-each-except
  [exception procedure ls]
  (loop [items ls]
    (cond (empty? items) :done
	  (= (first items) exception) (recur (rest items))
	  :else (do
		  (procedure (first items))
		  (recur (rest items))))))

(defrecord Constant [connector]
  Connection
  (has-value? [this] true)
  (get-value [this] (get-value connector))
  (set-value! [this new-value setter] (Error. "Unknown request - CONSTANT"))
  (forget-value! [this retractor] (Error. "Unknown request - CONSTANT"))
  (connect [this new-constraint] (Error. "Unknown request - CONSTANT")))

(defn make-constant [value connector]
  (let [constant (Constant. connector)]
    (connect connector constant)
    (set-value! connector value constant)
    constant))

(defrecord Connector [value informant constraints]
  Connection
  (has-value? [this] (if @informant true false))

  (get-value [this] @value)

  (set-value! [this new-value setter]
    (cond (not (has-value? this))
	  (do (swap! value (fn [x] new-value))
	      (swap! informant (fn [x] setter))
	      (for-each-except setter
			       inform-about-value
			       @constraints))
	  (not (= @value new-value))
	  (println (str "Contradiction! (" @value " " new-value ")"))
	  :else :ignored))

  (forget-value! [this retractor]
    (if (= retractor @informant)
        (do (swap! informant (fn [x] false))
	    (for-each-except retractor
			     inform-about-no-value
			     @constraints))
	:ignored))

  (connect [this new-constraint]
    (if (not (some #{new-constraint} @constraints))
        (swap! constraints #(cons new-constraint %)))
    (if (has-value? this)
        (inform-about-value new-constraint))
    :done))

(defn make-connector
  []
  (Connector. (atom false) (atom false) (atom '())))

(defrecord Multiplier [m1 m2 product]
  Constraint
  (process-new-value
   [this]
   (cond (or (and (has-value? m1) (zero? (get-value m1)))
	     (and (has-value? m2) (zero? (get-value m2))))
	 (set-value! product 0 this)
	 (and (has-value? m1) (has-value? m2))
	 (set-value! product
		     (* (get-value m1) (get-value m2))
		     this)
	 (and (has-value? product) (has-value? m1))
	 (set-value! m2
		     (/ (get-value product) (get-value m1))
		     this)
	 (and (has-value? product) (has-value? m2))
	 (set-value! m1
		     (/ (get-value product) (get-value m2))
		     this)))

  (process-forget-value
   [this]
   (forget-value! product this)
   (forget-value! m1 this)
   (forget-value! m2 this)
   (process-new-value this)))

(defn make-multiplier
  [m1 m2 product]
  (let [multiplier (Multiplier. m1 m2 product)]
    (connect m1 multiplier)
    (connect m2 multiplier)
    (connect product multiplier)))

(defrecord Adder [a1 a2 sum]
  Constraint
  (process-new-value
   [this]
   (cond (and (has-value? a1) (has-value? a2))
	 (set-value! sum
		     (+ (get-value a1) (get-value a2))
		     this)
	 (and (has-value? a1) (has-value? sum))
	 (set-value! a2
		     (- (get-value sum) (get-value a1))
		     this)
	 (and (has-value? a2) (has-value? sum))
	 (set-value! a1
		     (- (get-value sum) (get-value a2))
		     this)))

  (process-forget-value
   [this]
   (forget-value! a1 this)
   (forget-value! a2 this)
   (forget-value! sum this)
   (process-new-value this)))

(defn make-adder
  [a1 a2 sum]
  (let [adder (Adder. a1 a2 sum)]
    (connect a1 adder)
    (connect a2 adder)
    (connect sum adder)))

(defn averager
  [a b c]
  (let [sum (make-connector)
        divisor (make-connector)]
    (make-adder a b sum)
    (make-constant 2 divisor)
    (make-multiplier c divisor sum)))

;;; Exercise 3.35

(deftype Squarer [a b]
  Constraint
  (process-new-value
    [this]
    (if (has-value? b)
      (if (< (get-value b) 0)
        (Error. (str "square less than 0 -- SQUARER " (get-value b)))
        (set-value! a
                    (Math/sqrt (get-value b))
                    this))
      (when (has-value? a)
        (set-value! b
                    (square (get-value a))
                    this))))
  (process-forget-value
    [this]
    (forget-value! a this)
    (forget-value! b this)
    (process-new-value this)))

(defn make-squarer
  [a b]
  (let [squarer (Squarer. a b)]
    (connect a squarer)
    (connect b squarer)
    squarer))

;;; Exercise 3.37

(defn c+
  [x y]
  (let [z (make-connector)]
    (make-adder x y z)
    z))

(defn c-
  [x y]
  (let [z (make-connector)]
    (make-adder y z x)
    z))

(defn c*
  [x y]
  (let [z (make-connector)]
    (make-multiplier x y z)
    z))

(defn cd
  [x y]
  (let [z (make-connector)]
    (make-multiplier y z x)
    z))

(defn cv
  [x]
  (let [z (make-connector)]
    (make-constant x z)
    z))

;;; Exercise 3.47

(defn test-and-set!
  [cell]
  (if @cell
      true
      (do (swap! cell (fn [x] true))
	  false)))

(defn clear!
  [cell]
  (swap! cell (fn [x] false)))

(defn loop-test-and-set!
  [cell]
  (if (test-and-set! cell)
    (recur cell)))

(defn make-semaphore
  [n m]
  (let [count (atom n)
        cell (atom false)]
    (letfn [(aquire []
              (loop [still-need true]
                (clear! cell)
                (when still-need
                  (loop-test-and-set! cell)
                  (if (> 0 @count)
                    (do (swap! count dec)
                        (recur false))
                    (recur true)))))
            (release []
              (loop-test-and-set! cell)
              (if (< n @count) (swap! count inc))
              (clear! cell))]
      (cond (= m :aquire) (aquire)
            (= m :release) (release)))))

;;; Exercise 3.50

(defmacro cons-stream
  [el coll]
  (list 'lazy-seq (list cons el coll)))

(defn stream-map
  [proc coll & more]
  (let [argstreams (cons coll more)]
    (if (some true? (map empty? argstreams))
      '()
      (cons-stream
       (apply proc (map first argstreams))
       (apply stream-map proc (map rest argstreams))))))

;;; Exercise 3.51

(defn show
  [x]
  (println x)
  x)

; In clojure 'range and 'map are both lazy.
;(def x (map show (range 0 20)))

;(nth x 5)

;(nth x 17)

;;; Exercise 3.52

(defn display-stream
  [s]
  (doseq [x s]
    (println x)))

(def sum (atom 0))

(defn accum
  [x]
  (swap! sum #(+ x %))
  x)

;(def seqs (map accum (range 1 20)))

;(def y (filter even? seqs))

;(def x (filter (fn [x] (zero? (rem x 5))) seqs))

;;; Exercise 3.54

(defn mul-streams
  [x y]
  (map * x y))

(defn integers-starting-from
  [n]
  (iterate inc n))

(def factorials
  (lazy-seq
   (cons 1 (mul-streams factorials (integers-starting-from 2)))))

;;; Exercise 3.55

(defn partial-sum
  [s]
  (lazy-seq
   (cons
    (first s)
    (map +
         (next s)
         (partial-sum s)))))

;;; Exercise 3.56

(defn merge-streams
  [s1 s2]
  (cond (nil? s1) s2
        (nil? s2) s1
        :else (let [s1car (first s1)
                    s2car (first s2)]
                (cond (< s1car s2car)
                      (lazy-seq (cons s1car (merge-streams (next s1) s2)))
                      (> s1car s2car)
                      (lazy-seq (cons s2car (merge-streams s1 (next s2))))
                      :else (lazy-seq (cons s1car
                                            (merge-streams (next s1)
                                                           (next s2))))))))

(defn scale-stream
  [stream factor]
  (map #(* % factor) stream))

;;; Exercise 3.57

(defn add-streams
  [s1 s2]
  (map + s1 s2))

(def fibs
  (lazy-seq (cons 0
                  (lazy-seq (cons 1 (add-streams (rest fibs)
                                                 fibs))))))

;;; Exercise 3.58

(declare quotient)

(defn expand
  [num den radix]
  (lazy-seq
   (cons
    (quotient (* num radix) den)
    (expand (rem (* num radix) den) den radix))))

(defn quotient
  [x y] (int (/ x y)))

;;; Exercise 3.59

(defn integrate-series
  [s]
  ((fn iter [strm n]
     (lazy-seq
      (when-let [s (seq strm)]
        (cons (/ (first s) n)
              (iter (rest s) (inc n))))))
   s 1))

; Part b
(def exp-series (lazy-seq (cons 1
                                (integrate-series exp-series))))

(declare sine-series cosine-series)

(defn scale-series
  [s n]
  (map #(* % n) s))

(def cosine-series
  (lazy-seq (cons 1 (scale-series (integrate-series sine-series)
                                  -1))))

(def sine-series
  (lazy-seq (cons 0 (integrate-series cosine-series))))

;;; Exercise 3.60

(defn mul-series
  [s1 s2]
  (lazy-seq
   (cons (* (first s1) (first s2))
         (add-streams
          (scale-series (rest s2) (first s1))
          (mul-series (rest s1) s2)))))

;;; Exercise 3.61

(defn invert-unit-series
  [s]
  (lazy-seq
   (cons 1
         (scale-series
          (mul-series
           (invert-unit-series s)
           (rest s))
          -1))))

;;; Exercise 3.62

(defn div-series
  [top denom]
  (if (zero? (first denom)) (Error. "can't divide by zero"))
  (let [c (/ 1 (first denom))]
    (scale-series
     (mul-series top
                 (invert-unit-series (scale-series denom c)))
     c)))

(def tanget-series
  (div-series sine-series cosine-series))

;;; Exercise 3.63

(defn average
  [x y]
  (/ (+ x y) 2))

(defn sqrt-improve
  [guess x]
  (average guess (/ x guess)))

(defn sqrt-stream [x]
  ((fn guesses []
     (lazy-seq
      (cons 1.0
            (map (fn [guess] (sqrt-improve guess x))
                 (guesses)))))))

;;; Exercise 3.64

(defn stream-limit
  [strm tolerance]
  (let [x1 (first strm)
        x2 (second strm)
        diff (Math/abs (- x2 x1))]
    (if (< diff tolerance)
      x2
      (recur (nnext strm) tolerance))))

(defn sqrt
  [x tolerance]
  (stream-limit (sqrt-stream x) tolerance))

;;; Exercise 3.65

(defn square
  [x]
  (* x x))

(defn euler-transform
  [s]
  (let [s0 (nth s 0)
        s1 (nth s 1)
        s2 (nth s 2)]
    (lazy-seq
     (cons (- s2 (/ (square (- s2 s1))
                    (+ s0 (* -2 s1) s2)))
           (euler-transform (next s))))))

(defn make-tableau
  [transform s]
  (lazy-seq
   (cons s
         (make-tableau transform
                       (transform s)))))

(defn accelerated-sequence
  [transform s]
  (map first (make-tableau transform s)))

(def ln-2-summands
     (map double
          (map /
               (cycle '(1 -1))
               (iterate inc 1))))

(defn partial-sums
  [s]
  (lazy-seq
   (cons (first s) (map + (next s) (partial-sums s)))))

(def ln-2-stream
     (partial-sums ln-2-summands))

(def euler-ln-2-stream
     (euler-transform ln-2-stream))

(def accelerated-ln-2-stream
     (accelerated-sequence euler-transform ln-2-stream))

(defn stream-limit
  [strm tolerance n]
  (let [x1 (first strm)
        x2 (second strm)
        diff (Math/abs (- x2 x1))]
    (if (< diff tolerance)
      {:elem n :value x2}
(recur (nnext strm) tolerance (inc n)))))

;clojure-sicp.chapter3> (stream-limit euler-ln-2-stream 0.000000001 0)
                        ;{:elem 314, :value 0.6931471800635955}

;;; Exercise 3.66

(defn pairs
  [s t]
  (cons-stream
   [(first s) (first t)]
   (interleave
    (map #(vector (first s) %) (rest t))
    (pairs (rest s) (rest t)))))

;;; Exercise 3.67

(defn pairs
  [s t]
  (lazy-seq
   (cons
    (list (first s) (first t))
    (interleave
     (map (fn [x] (list (first s) x))
          (next t))
     (interleave
      (map (fn [x] (list x (first t)))
           (next s))
      (pairs (next s) (next t)))))))

;;; Exercise 3.68

(defn pairs-68
  [s t]
  (interleave
   (map (fn [x] (list (first s) x))
        t)
   (pairs (next s) (next t))))

;;; Exercise 3.69

(defn triples
  [s t u]
  (lazy-seq
   (cons
    (list (first s) (first t) (first u))
    (interleave
     (map (fn [x] (list* (first s) x))
          (next (pairs t u)))
     (triples (next s) (next t) (next u))))))


(defn pythagorean-triples
  []
  (filter (fn [x]
            (let [i (first x)
                  j (second x)
                  k (nth x 2)]
              (= (+ (square i)
                    (square j))
                 (square k))))
          (triples (iterate inc 1)
                   (iterate inc 1)
                   (iterate inc 1))))

;;; Exercise 3.70

(defn merge-weighted
  [weight s1 s2]
  (lazy-seq
   (cond (nil? s1) s2
         (nil? s2) s1
         :else
         (let [x1 (first s1), x2 (first s2)]
           (if (<= (weight x1) (weight x2))
             (cons x1 (merge-weighted weight (next s1) s2))
             (cons x2 (merge-weighted weight s1 (next s2))))))))

(defn weighted-pairs
  [weight s t]
  (lazy-seq
   (cons
    (list (first s) (first t))
    (merge-weighted weight
                    (map (fn [x] (list (first s) x))
                         (next t))
                    (weighted-pairs weight (next s) (next t))))))

;;; Exercise 3.71

(defn cube
  [x]
  (* x x x))

(defn sum-of-cubes-pair
  [[x y]]
  (+ (cube x) (cube y)))

(defn sum-of-cubes-stream
  []
  (weighted-pairs sum-of-cubes-pair
                  (iterate inc 1)
                  (iterate inc 1)))

(defn ramanujan-numbers
  []
  ((fn find-next [s]
     (lazy-seq
      (let [w1 (sum-of-cubes-pair (first s))
            w2 (sum-of-cubes-pair (second s))]
        (if (= w1 w2)
          (cons w1 (find-next (next s)))
          (find-next (next s))))))
   (sum-of-cubes-stream)))

;;; Exercise 3.72

(defn weight
  [i j]
  (+ (square i) (square j)))

(defn search-pairs
  [int-pairs]
  (let [x (nth int-pairs 0)
        y (nth int-pairs 1)
        z (nth int-pairs 2)]
    (if (= (weight x) (weight y) (weight z))
      (cons-stream [(weight x) [x y z]] (search-pairs (rest int-pairs)))
      (search-pairs (rest int-pairs)))))

;;; Exercise 3.73

(defn integral
  [integrand initial-value dt]
  ((fn inte []
     (lazy-seq
      (cons initial-value
            (add-streams
             (scale-stream integrand dt)
             (inte)))))))

(defn RC
  [R C dt]
  (fn [v0 i]
    (add-streams
     (scale-stream i R)
     (integral
      (scale-stream i (/ 1 C))
      v0
      dt))))

;;; Exercise 3.74

(defn  sign-change-detector
  [x y]
  (cond (and (neg? x) (pos? y)) 1
        (and (pos? x) (neg? y)) -1
        :else 0))

(defn zero-crossings
  [s]
  (map sign-change-detector (cons 0 s) s))

;;; Exercise 3.75

(defn make-zero-crossing
  [input-stream last-value last-avpt]
  (let [avpt (average (first input-stream) last-value)]
    (lazy-seq
     (cons (sign-change-detector avpt last-avpt)
           (make-zero-crossing (next input-stream)
                               (first input-stream)
                               avpt)))))

;;; Exercise 3.76

(defn average-every-two
  [s]
  (map #(/ (+ %1 %2) 2) (cons 0 s) s))

(defn smoothed-zero-crossings
  [s smooth]
  (map sign-change-detector (cons 0 (smooth s)) (smooth s)))

(defn smooth-by-averaging
  [s]
  (smoothed-zero-crossings s average-every-two))

;;; Exercise 3.77

(defn integral
  [delayed-integrand initial-value dt]
  (lazy-seq
   (cons initial-value
         (let [integrand (force delayed-integrand)]
           (if (nil? integrand)
             nil
             (integral
              (delay (rest integrand))
              (+ (* dt (first integrand))
                 initial-value)
              dt))))))

(defn solve
  [f y0 dt]
  (letfn [(y [] (integral (delay (dy)) y0 dt))
          (dy [] (map f (y)))]
    (y)))

;;; Exercise 3.78

(defn solve-2nd
  [a b dt y0 dy0]
  (letfn [(y [] (integral (delay (dy))  y0 dt))
          (dy [] (integral (delay (ddy)) dy0 dt))
          (ddy [] (add-streams
                   (scale-stream (dy) a)
                   (scale-stream (y) b)))]
    (y)))

;;; Exercise 3.79

(defn solve-2nd
  [f dt y0 dy0]
  (letfn [(y [] (integral (delay (dy)) y0 dt))
          (dy [] (integral (delay (ddy)) dy0 dt))
          (ddy [] (map f (dy) (y)))]
    (y)))

;;; Exercise 3.80

(defn RLC
  [R L C dt]
  (fn [vC0 iL0]
    (letfn [(iL [] (integral (delay (diL)) iL0 dt))
            (diL [] (add-streams
                     (scale-stream (iL) (- (/ R L)))
                     (scale-stream (vC) (/ 1 L))))
            (vC [] (integral (delay (dvC)) vC0 dt))
            (dvC [] (scale-stream (iL) (/ -1 C)))]
      (list (vC) (iL)))))

;;; Exercise 3.81

(defn rand-update
  [x]
  (let [a 9.4 b 5.7 m 3.2]
    (mod (+ (* a x)
            b)
         m)))

(defn gen-rand [cmds]
  ((fn me [next-value s]
     (lazy-seq
      (when-let [c (seq s)]
        (let [cmd (first c)]
          (cond (= :generate cmd)
                (cons next-value
                      (me (rand-update next-value)
                          (rest c)))
                (= :reset cmd)
                (cons (second c)
                      (me (rand-update (second c))
                          (rest (rest c)))))))))
   0.5 cmds))

;;; Exercise 3.82

(defn monte-carlo
  [experiment-stream passed failed]
  (letfn  [(nxt [passed failed]
             (lazy-seq
              (cons (/ passed (+ passed failed))
                    (monte-carlo
                     (rest experiment-stream) passed failed))))]
    (when (seq experiment-stream)
      (if (first experiment-stream)
        (nxt (inc passed) failed)
        (nxt passed (inc failed))))))

(defn random-in-range
  [low high]
  (+ low (rand (- high low))))

(defn rectangle-area
  [x1 x2 y1 y2]
  (Math/abs (* (- x2 x1) (- y2 y1))))

(defn estimate-integral
  [p x1 x2 y1 y2]
  (map #(* %
           (rectangle-area x1 x2 y1 y2))
       (monte-carlo
        (map p
             (repeatedly #(random-in-range x1 x2))
             (repeatedly #(random-in-range x1 x2)))
        0 0)))

(defn estimate-pi-using-area-unit-circle
  []
  (letfn [(square [x] (* x x))
          (unit-circle-predicate
            [x y]
            (<= (+ (square x) (square y)) 1))]
    (estimate-integral
     unit-circle-predicate -1.0 1.0 -1.0 1.0)))
