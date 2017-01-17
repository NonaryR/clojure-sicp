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
