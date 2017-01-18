(ns clojure-sicp.chapter2)

;;; Exercise 2.1

(defn gcd
  [a b]
  (if (= b 0)
    a
    (recur b (rem a b))))

(defn make-rat [n d]
  (let [g (gcd n d)
        rat (list (/ n g) (/ d g))]
    (println (first rat) "/" (last rat))))

;;; Exercise 2.2

(defn make-segment
  [start end]
  [start end])

(defn start-segment
  [segment]
  (first segment))

(defn end-segment
  [segment]
  (last segment))

(defn make-point
  [x y]
  [x y])

(defn x-point
  [point]
  (first point))

(defn y-point
  [point]
  (last point))

(defn midpoint-segment
  [segment]
  (make-point
   (/ (+ (x-point (start-segment segment))
         (x-point (end-segment segment)))
      2)
   (/ (+ (y-point (start-segment segment))
         (y-point (end-segment segment)))
      2)))

(defn print-point
  [p]
  (println (format "(%d, %d)"
                   (x-point p)
                   (y-point p))))

;; Exercise 2.3

(defn make-rectangle
  [length width]
  [length width])

(defn length [r]
  (first r))

(defn width [r]
  (last r))

(defn area [r]
  (* (length r)
     (width r)))

(defn perimeter [r]
  (* 2 (+ (length r)
          (width r))))

;;; Exercise 2.4

(defn my-cons
  [x y]
  (fn [m] (m x y)))

(defn my-car
  [lst]
  (lst (fn [x y] x)))

(defn my-cdr
  [lst]
  (lst (fn [x y] y)))

;;; Exercise 2.5

(defn my-cons
  [x y]
  (* (Math/pow 2 x)
     (Math/pow 3 y)))

(defn divides-count
  [n d]
  (loop [n (int n)
         cnt 0]
    (if (not= (mod n d) 0) cnt
        (recur (/ n d) (inc cnt)))))

(defn my-car
  [pair]
  (divides-count pair 2))

(defn my-cdr
  [pair]
  (divides-count pair 3))

;;; Exercise 2.6

(def zero
  (fn [f] (fn [x] x)))

(defn add-1
  [n]
  (fn [f] (fn [x] (f ((n f) x)))))

(def one (fn [f] (fn [x] (f x))))

(def two (fn [f] (fn [x] (f (f x)))))

;;; Exercise 2.7

(defn make-interval
  [a b]
  [a b])

(defn upper-bound
  [int]
  (first int))

(defn lower-bound
  [int]
  (second int))

(defn add-interval
  [x y]
  (make-interval (+ (lower-bound x) (lower-bound y))
                 (+ (upper-bound x) (upper-bound y))))

(defn mul-interval
  [x y]
  (let [p1 (* (lower-bound x) (lower-bound y))
        p2 (* (lower-bound x) (upper-bound y))
        p3 (* (upper-bound x) (lower-bound y))
        p4 (* (upper-bound x) (upper-bound y))]
    (make-interval (min p1 p2 p3 p4)
                   (max p1 p2 p3 p4))))

(defn div-interval
  [x y]
  (mul-interval x
                (make-interval (/ 1.0 (upper-bound y))
                               (/ 1.0 (lower-bound y)))))

;;; Exercise 2.8

(defn sub-interval
  [x y]
  (make-interval (- (lower-bound x) (upper-bound y))
                 (- (upper-bound x) (lower-bound y))))

;;; Exercise 2.10

(defn includes-zero?
  [interval]
  (and (<= (lower-bound interval) 0) (>= (upper-bound interval) 0)))

(defn div-interval
  [x y]
  (if (includes-zero? y)
    (throw (ArithmeticException. "Divide by zero"))
    (mul-interval x
                  (make-interval (/ 1.0 (upper-bound y))
                                 (/ 1.0 (lower-bound y))))))

;;; Exercise 2.11

(defn mul-interval
  [x y]
  (let [xlo (lower-bound x)
        xup (upper-bound x)
        ylo (lower-bound y)
        yup (upper-bound y)]
    (cond (and (>= xlo 0) (>= xup 0) (>= ylo 0) (>= yup 0)) ;; [+, +] * [+, +]
          (make-interval (* xlo ylo) (* xup yup))

          (and (>= xlo 0) (>= xup 0) (<= ylo 0) (>= yup 0)) ;; [+, +] * [-, +]
          (make-interval (* xup ylo) (* xup yup))

          (and (>= xlo 0) (>= xup 0) (<= ylo 0) (<= yup 0)) ;; [+, +] * [-, -]
          (make-interval (* xup ylo) (* xlo yup))

          (and (<= xlo 0) (>= xup 0) (>= ylo 0) (>= yup 0)) ;; [-, +] * [+, +]
          (make-interval (* xlo yup) (* xup yup))

          (and (<= xlo 0) (>= xup 0) (<= ylo 0) (>= yup 0)) ;; [-, +] * [-, +]
          (make-interval (min (* xup ylo) (* xlo yup))
                         (max (* xlo ylo) (* xup yup)))

          (and (<= xlo 0) (>= xup 0) (<= ylo 0) (<= yup 0)) ;; [-, +] * [-, -]
          (make-interval (* xup ylo) (* xlo ylo))

          (and (<= xlo 0) (<= xup 0) (>= ylo 0) (>= yup 0)) ;; [-, -] * [+, +]
          (make-interval (* xlo yup) (* xup ylo))

          (and (<= xlo 0) (<= xup 0) (<= ylo 0) (>= yup 0)) ;; [-, -] * [-, +]
          (make-interval (* xlo yup) (* xlo ylo))

          (and (<= xlo 0) (<= xup 0) (<= ylo 0) (<= yup 0)) ;; [-, -] * [-, -]
          (make-interval (* xup yup) (* xlo ylo)))))

;;; Exercise 2.12

(defn make-center-percent
  [c p]
  (let [ratio (/ p 100.0)]
    (make-interval (+ c (* c ratio))
                   (- c (* c ratio)))))

(defn center
  [i]
  (/ (+ (lower-bound i) (upper-bound i)) 2))

(defn percent
  [i]
  (let [width (- (upper-bound i) (center i))]
    (* 100 (/ width (center i)))))

;;; Exercise 2.13

(def small-perc1 (make-center-percent 9 2))

(def small-perc2 (make-center-percent 36 7))

;; (percent (mul-interval small-perc1 small-perc2))

;;; Exercise 2.14

(defn par1 [r1 r2]
  (div-interval (mul-interval r1 r2)
                (add-interval r1 r2)))

(defn par2 [r1 r2]
  (let [one (make-interval 1 1)]
    (div-interval one
                  (add-interval (div-interval one r1)
                                (div-interval one r2)))))

;;; Exercise 2.17

(defn last-pair
  [coll]
  (if (next coll)
    (recur (next coll))
    (first coll)))

;;; Exercise 2.18

(defn my-reverse
  [coll]
  (loop [c coll acc '()]
    (if c (recur (next c)
                 (conj acc (first c)))
        acc)))

;;; Exercise 2.19

(def us-coins (list 50 25 10 5 1))

(def uk-coins (list 100 50 20 10 5 2 1))

(defn no-more?
  [coin-values]
  (empty? coin-values))

(defn first-denomination
  [coin-values]
  (first coin-values))

(defn except-first-denomination
  [coin-values]
  (rest coin-values))

(defn cc
  [amount coin-values]
  (cond (= amount 0) 1
        (or (< amount 0) (no-more? coin-values)) 0
        :else (+ (cc amount (except-first-denomination coin-values))
                 (cc (- amount (first-denomination coin-values))
                     coin-values))))

;;; Exercise 2.20

(defn same-parity
  [x & xs]
  (cons x
        (filter (if (even? x) even? odd?) xs)))

;;; Exercise 2.21

(defn square
  [x]
  (* x x))

(defn square-list
  [coll]
  (if (nil? coll)
    nil
    (cons (square (first coll))
          (square-list (next coll)))))

(defn square-list
  [coll]
  (map square coll))

;;; Exercise 2.23

(defn for-each
  [f coll]
  (map f coll)
  nil)

(defn for-each
  [f coll]
  (doall (map f coll)) nil)

;;; Exercise 2.27

(defn deep-reverse
  [coll]
  (if (vector? coll)
    (map deep-reverse (reverse coll))
    coll))

;;; Exercise 2.28

(defn fringe [tree]
  (cond (nil? tree) []
        (not (coll? tree)) [tree]
        :else (concat (fringe (first tree))
                      (fringe (next tree)))))

;;; Exercise 2.29

(defn make-mobile
  [l r]
  (list l r))

(defn make-branch
  [length structure]
  (list length structure))

(defn left-branch
  [mobile]
  (first mobile))

(defn right-branch
  [mobile]
  (second mobile))

(defn branch-length
  [branch]
  (first branch))

(defn branch-structure
  [branch]
  (second branch))

(defn is-mobile?
  [mobile]
  (list? mobile))

(defn total-weight
  [mobile]
  (if (is-mobile? mobile)
    (let [l-branch-struct (branch-structure (left-branch mobile))
          r-branch-struct (branch-structure (right-branch mobile))]
      (+ (if (list? l-branch-struct)
           (total-weight l-branch-struct)
           l-branch-struct)
         (if (list? r-branch-struct)
           (total-weight r-branch-struct)
           r-branch-struct)))
    mobile))

(defn mobile-balanced?
  [mobile]
  (letfn [(torque [length weight] (* length weight))]
    (if (not (is-mobile? mobile)) true
        (let [l (left-branch mobile)
              r (right-branch mobile)]
          (and (= (torque (branch-length l)
                          (total-weight (branch-structure l)))
                  (torque (branch-length r)
                          (total-weight (branch-structure r))))
               (mobile-balanced? (branch-structure l))
               (mobile-balanced? (branch-structure r)))))))
