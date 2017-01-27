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


;;; Exercise 2.30

(defn square-tree
  [tree]
  (cond (nil? tree) nil
        (seq? tree) (cons (square-tree (first tree))
                          (square-tree (next tree)))
        :else (* tree tree)))

(defn square-tree-rec
  [tree]
  (if (seq? tree)
    (map square-tree tree)
    (* tree tree)))

;;; Exercise 2.31

(defn tree-map
  [f tree]
  (if (seq? tree)
    (map f tree)
    (f tree)))

(defn square-list
  [tree]
  (tree-map square tree))

;;; Exercise 2.32

(defn subsets
  [s]
  (if (nil? s) '(())
      (let [rest (subsets (next s))]
        (concat rest
                (map #(cons (first s) %) rest)))))

;;; Exercise 2.33

(defn my-map
  [f coll]
  (reduce #(concat %1 (list (f %2))) '() coll))

(defn my-append
  [coll1 coll2]
  (reduce conj coll2 (reverse coll1)))

(defn my-length
  [coll]
  (reduce (fn [x y] (inc x)) 0 coll))

;;; Exercise 2.34

(defn accumulate
  [op init coll]
  (if (nil? coll) init
      (op (first coll)
          (accumulate op init (next coll)))))

(defn horner-eval
  [x coefficient-sequence]
  (accumulate #(+ (* %2 x) %1) 0 coefficient-sequence))

;;; Exercise 2.35

(defn count-leaves
  [coll]
  (accumulate + 0 (map #(if (list? %)
                          (count-leaves %) 1)
                       coll)))

;;; Exercise 2.36

(defn accumulate-n
  [op init coll]
  (if (nil? (first coll))
    nil
    (cons (accumulate op init (map first coll))
          (accumulate-n op init (map next coll)))))

;;; Exercise 2.37

(defn dot-product
  [v w]
  (accumulate + 0 (map * v w)))

(defn matrix-*-vector
  [m v]
  (map (partial dot-product v) m))

(defn transpose
  [m]
  (accumulate-n cons nil m))

(defn matrix-*-matrix
  [m n]
  (let [cols (transpose n)]
    (map (fn [row] (map #(dot-product row %) cols)) m)))

;;; Exercise 2.39

(defn my-reverse
  [coll]
  (accumulate #(concat %2 (list %1)) nil coll))

(defn my-reverse
  [coll]
  (reduce #(cons %2 %1) nil coll))

;;; Exercise 2.40

(defn unique-pairs
  [n]
  (for [x (range 1 n) y (range (inc x) (inc n))]
    [x y]))

;;; Exercise 2.41

(defn unique-triples
  [n]
  (for [x (range 1 (dec n))
        y (range (inc x) n)
        z (range (inc y) (inc n))]
    [x y z]))

(defn sum
  [coll]
  (reduce + 0 coll))

(defn ex-2-41
  [n s]
  (let [trips (unique-triples n)]
    (filter #(= (sum %) s) trips)))

;;; Exercise 2.42

(def empty-board [])

(defn adjoin-position
  [new-row col rest-of-queens]
  (cons new-row rest-of-queens))

(defn safe?
  [k positions]
  (let [candidate (first positions)]
    (letfn [(safe-iter [top bot remain]
              (cond (empty? remain) true
                    (or (= (first remain) candidate)
                        (= (first remain) top)
                        (= (first remain) bot)) false
                    :else
                    (safe-iter (- top 1) (+ bot 1) (rest remain))))]
      (safe-iter (- candidate 1) (+ candidate 1) (rest positions)))))

(defn queens
  [board-size]
  (letfn [(queen-cols [k]
    (if (= k 0)
      (list empty-board)
      (filter (fn [positions] (safe? k positions))
              (mapcat
               (fn [rest-of-queens]
                 (map (fn [new-row]
                        (adjoin-position new-row k rest-of-queens))
                      (range 1 (inc board-size))))
               (queen-cols (dec k))))))]
  (queen-cols board-size)))

;;; Exercise 2.44

(defn below
  [p1 p2]
  :new-painter)

(defn beside
  [p1 p2]
  :new-painter)

(defn up-split
  [painter n]
  (if (= n 0)
    painter
    (let [smaller (up-split painter (- n 1))]
      (below painter (beside smaller smaller)))))

;;; Exercise 2.45

(defn split
  [a b]
  (fn ret [painter n]
    (if (= n 0)
      (let [smaller (ret painter (dec n))]
        (a painter (b smaller smaller))))))

(def right-split (split beside below))
(def up-split (split below beside))

;;; Exercise 2.46

(defn make-vect
  [x y]
  [x y])

(def xcor-vect first)
(def ycor-vect second)

(defn add-vect
  [v1 v2]
  (map + v1 v2))

(defn sub-vect
  [v1 v2]
  (map - v1 v2))

(defn scale-vect
  [v s]
  (map (partial * s) v))

;;; Exercise 2.47

(defn make-frame
  [origin edge1 edge2]
  [origin edge1 edge2])

(defn origin-frame
  [f]
  (f 0))

(defn edge1-frame
  [f]
  (f 1))

(defn edge2-frame
  [f]
  (f 2))

(defn make-frame
  [origin edge1 edge2]
  (cons origin [edge1 edge2]))

(defn origin-frame
  [f]
  (f 0))

(defn edge1-frame
  [f]
  ((f 0) 0))

(defn edge2-frame
  [f]
  ((f 0) 1))

;;; Exercise 2.48

(defn make-segment
  [start end]
  [start end])

(def start-segment first)
(def end-segment second)

;;; Exercise 2.49

(def outline-segments
 (list
  (make-segment (make-vect 0 0)
                (make-vect 0 1))
  (make-segment (make-vect 0 1)
                (make-vect 1 1))
  (make-segment (make-vect 1 1)
                (make-vect 1 0))
  (make-segment (make-vect 1 0)
                (make-vect 0 0))))

(def x-segments
 (list
  (make-segment (make-vect 0 0)
                (make-vect 1 1))
  (make-segment (make-vect 0 1)
                (make-vect 1 0))))

(def diamond-segments
 (list
  (make-segment (make-vect 0.5 0)
                (make-vect 0 0.5))
  (make-segment (make-vect 0 0.5)
                (make-vect 0.5 1))
  (make-segment (make-vect 0.5 1)
                (make-vect 1 0.5))
  (make-segment (make-vect 1 0.5)
                (make-vect 0.5 0))))

;; Exercise 2.50

(defn frame-coord-map
  [frame]
  (fn [v]
    (add-vect
     (origin-frame frame)
     (add-vect (scale-vect (xcor-vect v)
                           (edge1-frame frame))
               (scale-vect (ycor-vect v)
                           (edge2-frame frame))))))

(defn transform-painter
  [painter origin corner1 corner2]
  (fn [frame]
    (let [m (frame-coord-map frame) new-origin (m origin)]
      (painter (make-frame new-origin
                           (sub-vect (m corner1) new-origin)
                           (sub-vect (m corner2) new-origin))))))


(defn flip-horiz
  [painter]
  ((transform-painter (make-vect 1.0 0.0)
                      (make-vect 0.0 0.0)
                      (make-vect 1.0 1.0))
   painter))

(defn rotate180
  [painter]
  ((transform-painter (make-vect 1.0 1.0)
                      (make-vect 0.0 1.0)
                      (make-vect 1.0 0.0))
   painter))

(defn rotate270
  [painter]
  ((transform-painter (make-vect 0.0 1.0)
                      (make-vect 0.0 0.0)
                      (make-vect 1.0 1.0))
   painter))

;; Exercise 2.51

(defn beside
  [painter1 painter2]
  (let [split-point (make-vect 0.5 0.0)
        paint-left  (transform-painter painter1
                                       (make-vect 0.0 0.0)
                                       split-point
                                       (make-vect 0.0 1.0))
        paint-right (transform-painter painter2
                                       split-point
                                       (make-vect 1.0 0.0)
                                       (make-vect 0.5 1.0))]
    (fn [frame]
      (paint-left frame)
      (paint-right frame))))

(defn below
  [painter1 painter2]
  (let [split-point (make-vect 0.0 0.5)
        paint-bottom ((transform-painter
                       (make-vect 0.0 0.0)
                       (make-vect 1.0 0.0)
                       split-point) painter1)
        paint-top ((transform-painter
                    split-point
                    (make-vect 1.0 0.5)
                    (make-vect 0.0 1.0)) painter2)]
    (fn [frame]
      (paint-bottom frame)
      (paint-top frame))))

(defn rotate90
  [painter]
  ((transform-painter (make-vect 1.0 0.0)
                      (make-vect 1.0 1.0)
                      (make-vect 0.0 0.0))
   painter))

(defn below
  [painter1 painter2]
  (rotate90 (beside (rotate270 painter1) (rotate270 painter2))))

;;; Exercise 2.52

(defn corner-split
  [painter n]
  (if (= n 0)
    painter
    (let [up (up-split painter (- n 1))
          right (right-split painter (- n 1))
          corner (corner-split painter (- n 1))]
      (beside (below painter up)
              (below right corner)))))

(defn flip-vert
  [painter]
  (transform-painter painter
                     (make-vect 0.0 1.0)   ; new origin
                     (make-vect 1.0 1.0)   ; new end of edge1
                     (make-vect 0.0 0.0))) ; new end of edge2

(defn square-limit
  [painter n]
  (let [quarter (rotate180 (corner-split painter n))
        half (beside (flip-horiz quarter) quarter)]
    (below (flip-vert half) half)))

;;; Exercise 2.54

(defn equal?
  [a b]
  (cond
    (and (symbol? a) (symbol? b) (= a b)) true
    (and (coll? a) (coll? b) (= (first a) (first b))) (equal? (rest a) (rest b))
    :else false))

;; Exercise 2.55

(defn variable?
  [x]
  (symbol? x))

(defn same-variable?
  [v1 v2]
  (and (variable? v1) (variable? v2) (= v1 v2)))

(defn make-sum
  [a1 a2]
  (cond (= a1 0) a2
        (= a2 0) a1
        (and (number? a1) (number? a2)) (+ a1 a2)
        :else (list '+ a1 a2)))

(defn make-product
  [m1 m2]
  (cond (or (= m1 0) (= m2 0)) 0
        (= m1 1) m2
        (= m2 1) m1
        (and (number? m1) (number? m2)) (* m1 m2)
        :else (list '* m1 m2)))

(defn sum? [x]
  (and (coll? x) (= (first x) '+)))

(defn addend
  [s]
  (second s))

(defn augend
  [s]
  (second (rest s)))

(defn product? [x]
  (and (coll? x) (= (first x) '*)))

(defn multiplier
  [p]
  (second p))

(defn multiplicand
  [p]
  (second (rest p)))

(defn deriv [exp var]
  (cond (number? exp) 0
        (variable? exp) (if (same-variable? exp var) 1 0)
        (sum? exp) (make-sum (deriv (addend exp) var)
                             (deriv (augend exp) var))
        (product? exp) (make-sum
                        (make-product (multiplier exp)
                                      (deriv (multiplicand exp) var))
                        (make-product (deriv (multiplier exp) var)
                                      (multiplicand exp)))
:else (throw (Exception. "unknown expression type -- DERIV" exp))))


;;; Exercise 2.56

(defn exponentiation?
  [x]
  (and (coll? x) (= (first x) '**)))

(defn base
  [p]
  (second p))

(defn exponent
  [p]
  (second (rest p)))

(defn make-exponentiation
  [b e]
  (cond (= e 0) 1
        (= e 1) b
        (or (= b 1) (= b 0)) b
        :else (list '** b e)))

(defn deriv
  [exp var]
  (cond (number? exp) 0
        (variable? exp) (if (same-variable? exp var) 1 0)
        (sum? exp) (make-sum (deriv (addend exp) var)
                             (deriv (augend exp) var))
        (product? exp) (make-sum
                        (make-product (multiplier exp)
                                      (deriv (multiplicand exp) var))
                        (make-product (deriv (multiplier exp) var)
                                      (multiplicand exp)))
        (exponentiation? exp) (make-product
                               (make-product (exponent exp)
                                             (make-exponentiation (base exp) (dec (exponent exp))))
                               (deriv (base exp) var)
                               )
        :else (throw (Exception. "Unknown expression - DERIV" exp))))

;;; Exercise 2.57

(defn addend
  [s]
  (first s))

(defn augend
  [s]
  (second (rest s)))

;;; Exercise 2.58

(defn make-sum [a1 a2]
  (cond (= a1 0) a2
        (= a2 0) a1
        (and (number? a1) (number? a2)) (+ a1 a2)
        :else (list a1 '+ a2)))

(defn make-product [m1 m2]
  (cond (or (= m1 0) (= m2 0)) 0
        (= m1 1) m2
        (= m2 1) m1
        (and (number? m1) (number? m2)) (* m1 m2)
        :else (list m1 '* m2)))

(defn sum? [x]
  (and (coll? x) (= (second x) '+)))

(defn product? [x]
  (and (coll? x) (= (second x) '*)))

(defn base [p] (first p))

(defn make-exponentiation [b e]
  (cond (= e 0) 1
        (= e 1) b
        (or (= b 1) (= b 0)) b
        :else (list b '** e)))

;;; Exercise 2.59

(defn element-of-set?
  [x set]
  (cond (empty? set) false
        (= x (first set)) true
        :else (element-of-set? x (rest set))))

(defn union-set
  [set1 set2]
  (cond
    (empty? set1) set2
    (element-of-set? (first set1) set2) (union-set (rest set1) set2)
    :else (union-set (rest set1) (cons (first set1) set2))))

;;; Exercise 2.60

(defn adjoin-set [x set]
  (if (element-of-set? x set)
    set
    (cons x set)))

(defn intersection-set
  [set1 set2]
  (cond (or (empty? set1) (empty? set2)) '()
        (element-of-set? (first set1) set2) (cons (first set1)
                                                  (intersection-set (rest set1) set2))
        :else (intersection-set (rest set1) set2)))

;;; Exercise 2.61

(defn element-of-set?
  [x set]
  (cond (empty? set) false
        (= x (first set)) true
        (< x (first set)) false
        :else (element-of-set? x (rest set))))

;;; Exercise 2.62

(defn union-set
  [set1 set2]
  (cond
    (empty? set1) set2
    (empty? set2) set1
    :else (let [x1 (first set1) x2 (first set2)]
            (cond (= x1 x2) (cons x1 (union-set (rest set1) (rest set2)))
                  (< x1 x2) (cons x1 (union-set (rest set1) set2))
                  (< x2 x1) (cons x2 (union-set set1 (rest set2)))))))

;;; Exercise 2.63
;; !!NEED TEST

(defn entry
  [tree]
  (tree 0))

(defn left-branch
  [tree]
  (tree 1))

(defn right-branch
  [tree]
  (tree 2))

(defn make-tree
  [entry left right]
  [entry left right])

(defn tree->list-1
  [tree]
  (if (empty? tree) []
      (concat (tree->list-1 (left-branch tree))
              (cons (entry tree)
                    (tree->list-1 (right-branch tree))))))

(defn tree->list-2
  [tree]
  (letfn [(copy-to-list [tree result-list]
    (if (empty? tree) result-list
        (copy-to-list (left-branch tree)
                      (cons (entry tree)
                            (copy-to-list (right-branch tree)
                                          result-list)))))]
  (copy-to-list tree [])))

;;; Exercise 2.64

(defn partial-tree
  [elts n]
  (if (= n 0) ([[] elts])
      (let [left-size (quot (dec n) 2)
            left-result (partial-tree elts left-size)
            left-tree (first left-result)
            non-left-elts (second left-result)
            right-size (- n (inc left-size))
            this-entry (first non-left-elts)
            right-result (partial-tree (rest non-left-elts) right-size)
            right-tree (first right-result)
            remaining-elts (second right-result)]
        [(make-tree this-entry left-tree right-tree) remaining-elts])))

(defn list->tree
  [elements]
  (first (partial-tree elements (count elements))))

;;; Exercise 2.66

(defn lookup
  [given-key set-of-records]
  (cond
    (empty? set-of-records) false
    (= given-key (key (entry set-of-records))) (entry set-of-records)
    (< given-key (key (entry set-of-records))) (lookup given-key (left-branch set-of-records))
    (> given-key (key (entry set-of-records))) (lookup given-key (right-branch set-of-records))))

;;; Exercise 2.67

(defn make-leaf
  [symbol weight]
  ['leaf symbol weight])

(defn leaf?
  [object]
  (= (object 0) 'leaf))

(defn symbol-leaf
  [x]
  (x 1))

(defn weight-leaf
  [x]
  (x 2))

(defn symbols
  [tree]
  (if (leaf? tree)
    [(symbol-leaf tree)]
    (tree 2)))

(defn left-branch
  [tree]
  (tree 0))

(defn right-branch
  [tree]
  (tree 1))

(defn weight
  [tree]
  (if (leaf? tree)
    (weight-leaf tree)
    (tree 3)))

(defn make-code-tree
  [left right]
  [left right
   (concat (symbols left) (symbols right))
   (+ (weight left) (weight right))])

(defn choose-branch [bit branch]
  (cond (= bit 0) (left-branch branch)
        (= bit 1) (right-branch branch)))

(defn decode
  [bits tree]
  (letfn [(decode-1 [bits current-branch]
    (if (empty? bits) []
      (let [next-branch (choose-branch (first bits) current-branch)]
        (if (leaf? next-branch)
          (cons (symbol-leaf next-branch)
                (decode-1 (rest bits) tree))
          (decode-1 (rest bits) next-branch)))))]
  (decode-1 bits tree)))

(defn adjoin-set
  [x set]
  (cond
   (empty? set) [x]
   (< (weight x) (weight (first set))) (cons x set)
   :else (cons (first set) (adjoin-set x (rest set)))))

(defn make-leaf-set
  [pairs]
  (if (empty? pairs) []
    (let [pair (first pairs)]
      (adjoin-set (make-leaf (first pair)   ;;; symbol
                             (second pair)) ;;; freq
                  (make-leaf-set (rest pairs))))))

;;; Exercise 2.68

(defn memq
  [item x]
  (cond (empty? x) false
        (= item (first x)) x
        :else (memq item (rest x))))

(defn encode-symbol
  [symbol tree]
  (defn in-branch? [branch]
    (if (leaf? branch)
      (= symbol (symbol-leaf branch))
      (memq symbol (symbols branch))))
  (let [lb (left-branch tree)
        rb (right-branch tree)]
    (cond (in-branch? lb)  (if (leaf? lb) [0] (cons 0 (encode-symbol symbol lb)))
          (in-branch? rb)  (if (leaf? rb) [1] (cons 1 (encode-symbol symbol rb)))
          :else (throw (RuntimeException. (str "Can't encode symbol -> " symbol))))))

(defn encode
  [message tree]
  (if (empty? message) []
      (concat (encode-symbol (first message) tree)
              (encode (rest message) tree))))

;;; Exercise 2.69

(defn successive-merge
  [trees]
  (if (= 1 (count trees))
    (first trees)
    (let [a (first trees)
          b (second trees)
          remainder (drop 2 trees)
          new-tree (make-code-tree a b)
          new-trees (adjoin-set new-tree remainder)]
      (successive-merge new-trees))))

(defn generate-huffman-tree
  [pairs]
  (successive-merge (make-leaf-set pairs)))

;;; Exercise 2.70

(def rock-tree (generate-huffman-tree #{'(a 2) '(boom 1) '(Get 2) '(job 2) '(na 16) '(Sha 3) '(yip 9) '(Wah 1)}))

(def rock-lyric '(Get a job
                      Sha na na na na na na na na
                      Get a job
                      Sha na na na na na na na na
                      Wah yip yip yip yip yip yip yip yip yip
                      Sha boom))

(def encoded-lyric (encode rock-lyric rock-tree))

;; (< (count encoded-lyric) (* 3 (count rock-lyric)))

;; Exercise 2.73

(defn variable?
  [e]
  (symbol? e))

(defn same-variable?
  [v1 v2]
 (and (variable? v1) (variable? v2) (= v1 v2)))

(defn =number?
  [x n]
 (and (number? x) (= x n)))

(defn make-sum
  [a1 a2]
 (cond (=number? a1 0) a2
  (=number? a2 0) a1
  (and (number? a1) (number? a2)) (+ a1 a2)
  :else (list '+ a1 a2)))

(defn addend
  [s]
  (second s))

(defn augend [s]
  (first (rest (rest s))))

(defn make-product
  [m1 m2]
 (cond (or (=number? m1 0) (=number? m2 0)) 0
       (=number? m1 1) m2
       (=number? m2 1) m1
       (and (number? m1) (number? m2)) (* m1 m2)
       :else (list '* m1 m2)))

(defn multiplier
  [p]
  (second p))

(defn multiplicand
  [p]
  (first (rest (rest p))))

(defn operator
  [exp]
  (first exp))

(defn operands [exp] (rest exp))

(defmulti do-deriv
  (fn [exp v] (operator exp)))

(defmethod do-deriv '+
 [exp v]
 (make-sum (deriv (addend exp) v)
  (deriv (augend exp) v)))

(defmethod do-deriv '*
 [exp v]
 (make-sum
  (make-product (multiplier exp)
                (deriv (multiplicand exp) v))
  (make-product (deriv (multiplier exp) v)
                (multiplicand exp))))

(defn deriv
  [exp v]
 (cond (number? exp) 0
       (variable? exp) (if (same-variable? exp v) 1 0)
:else (do-deriv exp v)))

;;; Exercise 2.74 -- TO DO

;;; Exercise 2.75

(defn apply-generic
  [op arg]
  (arg op))

(defn make-from-mag-ang
  [m a]
  (fn dispatch [op]
    (cond
     (= op 'real-part) (* m (Math/cos a))
     (= op 'imag-part) (* m (Math/sin a))
     (= op 'magnitude) m
     (= op 'angle) a
     :else (throw (RuntimeException. (str "Unknown op - MAKE-FROM-REAL-IMAG" op))))))

;;; Exercise 2.77

(def proc-table (atom {}))

(defn pt-get
  [op type]
  (@proc-table [op type]))

(defn pt-put
  [op type item]
  (swap! proc-table #(assoc % [op type] item)))

(defn attach-tag
  [tag content]
  (if (coll? content) (cons tag content) content))

(defn type-tag
  [datum]
  (cond (number? datum) datum
        (coll? datum) (first datum)
        :else (throw (RuntimeException. (str "Wrong datum -- TYPE-TAG " datum)))))

(defn contents
  [datum]
  (cond (number? datum) datum
        (coll? datum) (rest datum)
        :else (throw (RuntimeException. (str "Wrong datum -- CONTENGS " datum)))))

(defn install-rectangular-package
  []
  (let [real-part (fn [z] (first z))
        imag-part (fn [z] (second z))
        make-from-real-imag (fn [x y] [x y])
        magnitude (fn [z]
                    (Math/sqrt (+ (#(* % %) (real-part z))
                                  (#(* % %) (imag-part z)))))
        angle (fn [z]
                (Math/atan2 (imag-part z) (real-part z)))
        make-from-mag-ang (fn [r a]
                            [(* r (Math/cos a))
                             (* r (Math/sin a))])
        tag (fn [x] (attach-tag 'rectangular x))]

    (pt-put 'real-part '(rectangular) real-part)
    (pt-put 'imag-part '(rectangular) imag-part)
    (pt-put 'magnitude '(rectangular) magnitude)
    (pt-put 'angle '(rectangular) angle)
    (pt-put 'make-from-real-imag 'rectangular
            (fn [x y] (tag (make-from-real-imag x y))))
    (pt-put 'make-from-mag-ang 'rectangular
            (fn [r a] (tag (make-from-mag-ang r a))))))

(defn install-polar-package
  []
  (let [magnitude (fn [z] (first z))
        angle (fn [z] (second z))
        make-from-mag-ang (fn [r a] [r a])
        real-part (fn [z]
                    (* (magnitude z) (Math/cos (angle z))))
        imag-part (fn [z]
                    (* (magnitude z) (Math/sin (angle z))))
        make-from-real-imag (fn [x y]
                              [(Math/sqrt (+ (#(* % %) x) (#(* % %) y)))
                               (Math/atan2 y x)])
        tag (fn [x] (attach-tag 'polar x))]


    (pt-put 'real-part '(polar) real-part)
    (pt-put 'imag-part '(polar) imag-part)
    (pt-put 'magnitude '(polar) magnitude)
    (pt-put 'angle '(polar) angle)
    (pt-put 'make-from-real-imag 'polar
            (fn [x y] (tag (make-from-real-imag x y))))
    (pt-put 'make-from-mag-ang 'polar
            (fn [r a] (tag (make-from-mag-ang r a))))))


(defn apply-generic
  [op & args]
  (let [type-tags (map type-tag args)
        proc (pt-get op type-tags)]
    (if proc
      (apply proc (map contents args))
      (throw (RuntimeException. (str "No method for -- " op type-tags))))))

(defn real-part
  [z]
  (apply-generic 'real-part z))

(defn imag-part
  [z]
  (apply-generic 'imag-part z))

(defn magnitude
  [z]
  (apply-generic 'magnitude z))

(defn angle
  [z]
  (apply-generic 'angle z))

(defn add
  [x y]
  (apply-generic 'add x y))

(defn sub
  [x y]
  (apply-generic 'sub x y))

(defn mul
  [x y]
  (apply-generic 'mul x y))

(defn div
  [x y]
  (apply-generic 'div x y))

(defn install-scheme-number-package
  []
  (let [tag (fn [x]
              (attach-tag 'scheme-number x))]

    (pt-put 'add '(scheme-number scheme-number)
            (fn [x y] (tag (+ x y))))
    (pt-put 'sub '(scheme-number scheme-number)
            (fn [x y] (tag (- x y))))
    (pt-put 'mul '(scheme-number scheme-number)
            (fn [x y] (tag (* x y))))
    (pt-put 'div '(scheme-number scheme-number)
            (fn [x y] (tag (/ x y))))
    (pt-put 'make 'scheme-number
            (fn [x] (tag x)))))

(defn make-scheme-number
  [n]
  ((pt-get 'make 'scheme-number) n))

(defn install-rational-package
  []
  (let [numer (fn [x] (first x))
        denom (fn [x] (second x))
        make-rat (fn [n d] (let [g (gcd n d)] [(/ n g) (/ d g)]))
        add-rat (fn [x y]
                  (make-rat (+ (* (numer x) (denom y))
                               (* (numer y) (denom x)))
                            (* (denom x) (denom y))))
        sub-rat (fn [x y]
                  (make-rat (- (* (numer x) (denom y))
                               (* (numer y) (denom x)))
                            (* (denom x) (denom y))))
        mul-rat (fn [x y]
                  (make-rat (* (numer x) (numer y))
                            (* (denom x) (denom y))))
        div-rat (fn [x y]
                  (make-rat (* (numer x) (denom y))
                            (* (denom x) (numer y))))
        tag (fn [x] (attach-tag 'rational x))]
    (pt-put 'add '(rational rational)
            (fn [x y] (tag (add-rat x y))))
    (pt-put 'sub '(rational rational)
            (fn [x y] (tag (sub-rat x y))))
    (pt-put 'mul '(rational rational)
            (fn [x y] (tag (mul-rat x y))))
    (pt-put 'div '(rational rational)
            (fn [x y] (tag (div-rat x y))))
    (pt-put 'make 'rational
            (fn [n d] (tag (make-rat n d))))))

(defn make-rational
  [n d]
  ((pt-get 'make 'rational) n d))

(defn install-complex-package
  []
  (let [make-from-real-imag (fn [x y]
                              ((pt-get 'make-from-real-imag 'rectangular) x y))
        make-from-mag-ang (fn [r a]
                            ((pt-get 'make-from-mag-ang 'polar) r a))
        add-complex (fn [z1 z2]
                      (make-from-real-imag (+ (real-part z1) (real-part z2))
                                           (+ (imag-part z1) (imag-part z2))))
        sub-complex (fn [z1 z2]
                      (make-from-real-imag (- (real-part z1) (real-part z2))
                                           (- (imag-part z1) (imag-part z2))))
        mul-complex (fn [z1 z2]
                      (make-from-mag-ang (* (magnitude z1) (magnitude z2))
                                         (+ (angle z1) (angle z2))))
        div-complex (fn [z1 z2]
                      (make-from-mag-ang (/ (magnitude z1) (magnitude z2))
                                         (- (angle z1) (angle z2))))
        tag (fn [z] (attach-tag 'complex z))]
    (pt-put 'add '(complex complex)
            (fn [z1 z2] (tag (add-complex z1 z2))))
    (pt-put 'sub '(complex complex)
            (fn [z1 z2] (tag (sub-complex z1 z2))))
    (pt-put 'mul '(complex complex)
            (fn [z1 z2] (tag (mul-complex z1 z2))))
    (pt-put 'div '(complex complex)
            (fn [z1 z2] (tag (div-complex z1 z2))))
    (pt-put 'make-from-real-imag 'complex
            (fn [x y] (tag (make-from-real-imag x y))))
    (pt-put 'make-from-mag-ang 'complex
            (fn [r a] (tag (make-from-mag-ang r a))))))

(defn make-complex-from-real-imag
  [x y]
  ((pt-get 'make-from-real-imag 'complex) x y))

(defn make-complex-from-mag-ang
  [r a]
  ((pt-get 'make-from-mag-ang 'complex) r a))

;; (def z (make-complex-from-mag-ang 8 6))

;; Fails
;;(magnitude z)

;;(pt-put 'real-part '(complex) real-part)
;;(pt-put 'imag-part '(complex) imag-part)
;;(pt-put 'magnitude '(complex) magnitude)
;;(pt-put 'angle '(complex) angle)

;;(magnitude z)

;;; Exercise 2.78

(defn attach-tag
  [tt contents]
  (if (number? contents) contents
      (cons tt contents)))

(defn type-tag
  [datum]
  (cond (number? datum) 'scheme-number
        (seq? datum) (first datum)
        :else (Error. (str "Bad tagged datum -- TYPE-TAG " datum))))

(defn contents
  [datum]
  (cond (number? datum) datum
        (seq? datum) (rest datum)
        :else (Error. (str "Bag tagged datum -- CONTENTS " datum))))

;;; Exercise 2.79

(defn equ?
  [x y]
  (apply-generic 'equ? x y))

#_(pt-put 'equ? '(scheme-number scheme-number)
     (fn [x y] (= x y)))

;; Exercise 2.80

(defn =zero?
  [x]
  (apply-generic '=zero? x))

;; Exercise 2.81

(defn put-coercion [source-type target-type proc]
  (pt-put 'coercion [source-type target-type] proc))

(defn get-coercion [source-type target-type]
  (pt-get 'coercion [source-type target-type]))

(defn scheme-number->complex [n]
  (make-complex-from-real-imag (contents n) 0))

;;(put-coercion 'scheme-number 'complex scheme-number->complex)

(defn apply-generic [op & args]
  (letfn [(no-method [type-tags]
    (throw (RuntimeException. (str "No method for -- " op " -- " type-tags))))]
    (let [type-tags (map type-tag args)
          proc (pt-get op type-tags)]
      (if proc
        (apply proc (map contents args))
        (if (= (count args) 2)
          (let [type1 (first type-tags)
                type2 (second type-tags)
                a1 (first args)
                a2 (second args)]
            (if (= type1 type2)
              (no-method type-tags)
              (let [t1->t2 (get-coercion type1 type2)
                    t2->t1 (get-coercion type2 type1)]
                (cond
                  t1->t2 (apply-generic op (t1->t2 a1) a2)
                  t2->t1 (apply-generic op a1 (t2->t1 a2))
                  :else (no-method type-tags)))))
          (no-method type-tags))))))

;; Exercise 2.82

(defn all-can-convert-to?
  [target types]
 (every? true?
         ((map (fn [t] (or (= t target)
                       (get-coercion t target))))
         types)))

(defn find-a-common-type
  [types]
 (letfn [(first-true [bs ts]
          (cond (zero? (count bs)) nil
                (true? (first bs)) (first ts)
                :else (recur (rest bs) (rest ts))))]
   (map (fn [target] (all-can-convert-to? target types))
        types)))

(defn convert-all-to
  [desired-type args]
 (map (fn [a]
       (let [current-type (type-tag a)]
        (if (= desired-type current-type) 
            a
            ((get-coercion current-type desired-type) a))))
      args))

(defn apply-generic
  [op & args]
 (let [type-tags (map type-tag args)
       no-method-error #(Error. (str "No method for these types " (list op type-tags)))
       proc (get op type-tags)]
  (if proc
      (apply proc (map contents args)) 
      (let [common-type (find-a-common-type type-tags)]
       (if common-type
           (apply
            (apply-generic 
             (list* op 
                   (convert-all-to common-type args)))))
       (no-method-error)))))

;; Exercise 2.83

(defn integer->rational
  [x]
  (make-rational x 1))

(defn raise
  [x]
  ((get 'raise (type-tag x)) x))

;; Exercise 2.84

(declare type-tag)
(declare contents)
(declare get-coercion)

(defn apply-generic
  [op & args]
 (letfn [(multi-raise [begin target]
          (let [begin-type (type-tag begin)
                target-type (type-tag target)]
            (cond (= begin-type target-type) begin
                  (get 'raise (list begin-type))
                    (multi-raise ((get 'raise (list begin-type)) begin target)))
                  :else nil))
         (no-method-error [tags]
            (Error. (str "No method for these types " (list op tags))))]
 (let [type-tags (map type-tag args)
       proc (get op type-tags)]
  (if proc
      (apply proc (map contents args)) 
      (if (= (count args) 2)
          (let [type1 (first type-tags)
                type2 (second type-tags)
                a1 (first args)
                a2 (second args)
                t1->t2 (get-coercion type1 type2)
                t2->t1 (get-coercion type2 type1)]
            (cond (= type1 type2) (no-method-error type-tags)
                  (multi-raise a1 a2) (apply-generic op (multi-raise a1 a2) a2)
                  (multi-raise a2 a1) (apply-generic op a1 (multi-raise a2 a1))
                  :else (Error. (str "No method for these types " (list op type-tags)))))
          (no-method-error type-tags))))))
