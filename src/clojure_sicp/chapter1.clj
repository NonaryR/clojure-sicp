(ns clojure-sicp.chapter1)

;;; Exercise 1.2

(/ (+ 5 4 (- 2 (- 3 (+ 6 (/ 4 5)))))
   (* 3 (- 6 2) (- 2 7)))

;;; Exercise 1.3

(defn sum-square-bigger
  [a b c]
  (letfn [(square [n] (* n n))]
    (- (apply + (map square [a b c]))
       (square (min a b c)))))

;;; Exercise 1.7

(defn good-enough?
  [old-guess new-guess]
  (< (/ (Math/abs (- old-guess new-guess))
        old-guess)
     0.001))

(defn average
  [x y]
  (/ (+ x y) 2))

(defn improve-sq
  [guess n]
  (average guess (/ n guess)))

(defn sqrt [n]
  (letfn [(sqrt-iter [guess]
            (let [new (improve-sq guess n)]
              (if (good-enough? guess new)
                new
                (sqrt-iter new))))]
    (sqrt-iter 1.0)))

;;; Exercise 1.8

(defn cube
  [x]
  (Math/pow x 3))

(defn improve-cube
  [guess x]
  (/ (+ (/ x (* guess guess))
        (* 2 guess))
     3))

(defn cubert [x]
  (letfn [(cubert-iter [guess x]
            (if (good-enough? (cube guess) x)
              guess
              (cubert-iter (improve-cube guess x) x)))]
    (cubert-iter 1.0 x)))

;;; Exercise 1.11

(defn f-recursive [n]
  (if (< n 3) n
      (+ (f-recursive (- n 1))
         (f-recursive (- n 2))
         (f-recursive (- n 3)))))

(defn f-iterate [n]
  (letfn [(f-help [n1 n2 n3 cnt]
            (if (= cnt n) (+ n1 n2 n3)
                (f-help n2 n3 (+ n1 n2 n3) (inc cnt))))]
    (if (< n 3) n
        (f-help 0 1 2 3))))

;;; Exercise 1.12

(defn pascal
  [row col]
  (cond (= row 0) (if (= col 0) 1 (throw (Exception. "Out of range")))
        (= col 0) 1
        (= col row) 1
        (> row 1) (if (or (< col 0) (> col row))
                    (throw (Exception. "Out of range"))
                    (+ (pascal (dec row) (dec col))
                       (pascal (dec row) col)))
        :else (throw (Exception. "Out of range"))))

(for [row (range 0 10)
      col (range 0 (inc row))]
  (pascal row col))

;;; Exercise 1.16

(defn square [n] (* n n))

(defn fast-expt-iter
  [b n]
  (letfn [(help [a b n]
            (cond (= n 0) a
                  (even? n) (help a (square b) (/ n 2))
                  (odd? n) (help (* a b) b (dec n))))]
    (help 1 b n)))

(every? identity
        (for [x (range 0 10) y (range 0 10)]
          (= (fast-expt-iter x y) (int (Math/pow x y)))))

;;; Exercise 1.17

(defn double-n
  [n]
  (* 2 n))

(defn halve
  [n]
  (when (even? n) (/ n 2)))

(defn fast-mult-rec
  [a b]
  (cond (= b 1) a
        (= a 1) b
        (even? b) (double-n (fast-mult-rec a (halve b)))
        :else (+ a (fast-mult-rec a (dec b)))))

;;; Exercise 1.18

(defn fast-mult-iter
  [a b]
  (letfn [(help [a b c]
            (cond (= b 0) c
                  (even? b) (help (double-n a) (halve b) c)
                  (odd? b) (help a (dec b) (+ c a))))]
    (help a b 0)))

;;; Exercise 1.19

(defn fib
  [n]
  (letfn [(fib-iter [a b p q counter]
            (cond (= counter 0) b
                  (even? counter) (fib-iter a b
                                          (+ (* p p) (* q q))
                                          (+ (* q q) (* 2 p q))
                                          (/ counter 2))
                  :else (fib-iter (+ (* b q) (* a q) (* a p))
                                  (+ (* b p) (* a q))
                                  p
                                  q
                                  (- counter 1))))]
    (fib-iter 1 0 0 1 n)))

;;; Exercise 1.21 + 1.22 + 1.24

(defn expmod
  [base exp m]
  (cond (= exp 0) 1
        (even? exp) (mod (square (expmod base (/ exp 2) m))
                         m)
        :else (mod (* base (expmod base (dec exp) m))
                   m)))

(defn fermat-test
  [n]
  (let [rand (int (inc (rand (dec n))))]
    (= (expmod rand n n) rand)))

(defn fast-prime?
  [n times]
  (every? identity
          (map fermat-test (take times (repeat n)))))

(defn search-for-primes
  [from to]
  (let [table (map #(vector % (fast-prime? % 20)) (range from to))]
    (map first (filter second table))))

;; (time (search-for-primes 1000 10000))
;; "Elapsed time: 0.237468 msecs"

;; (time (search-for-primes 100000 1000000))
;; "Elapsed time: 0.048391 msecs"


;;; Exercise 1.23

(defn smallest-divisor
  [n]
  (letfn [(find-divisor [test]
            (letfn [(next-test [n]
                      (if (= n 2) 3
                          (+ n 2)))]
              (cond (> (square test) n) n
                    (= (mod n test) 0) test
                    :else (find-divisor (next-test test)))))]
    (find-divisor 2)))

(defn prime?
  [n]
  (= n (smallest-divisor n)))

;;; Exercise 1.27

(defn test-ferma?
  [n]
  (and (not (prime? n))
       (every? #(= (expmod % n n) %)
               (range 1 n))))

;; Exercise 1.28

(defn mill-rabin-expmod
  [base exp m]
  (cond (= exp 0) 1
        (even? exp) (let [itr (mill-rabin-expmod base (/ exp 2) m)
                          sqr (square itr)]
                      (if (and (not= itr 1)
                               (not= itr (dec m))
                               (= sqr (mod 1 m)))
                        0
                        (mod sqr m)))
        :else (mod (* base (mill-rabin-expmod base (dec exp) m))
                   m)))

(defn mr-fermat-test
  [n]
  (let [rand (int (inc (rand (dec n))))]
    (= (mill-rabin-expmod rand (dec n) n) (mod 1 n))))

(defn mr-fast-prime?
  [n times]
  (every? mr-fermat-test
          (take times (repeat n))))

(let [in [11 332 321 12 9 754 1376 10098]
      out [true false false false false false false false]]
  (= out (map #(mr-fast-prime? % 20) in)))

;;; Exercise 1.29

(defn sum
  [term a next b]
  (if (> a b)
    0
    (+ (term a)
       (sum term (next a) next b))))

(defn integral
  [f a b n]
  (let [h (/ (- b a) n)]
    (letfn [(term [k]
              (* (f (+ a (* k h)))
                 (if (even? k) 2 4)))]
      (/ (* h
            (+ a (sum term 1 inc n)))
         3))))

;;; Exercise 1.30

(defn sum-it
  [term a next b]
  (loop [a a
         acc 0]
    (if (> a b) acc
        (recur (next a) (+ acc (term a))))))


;;; Exercise 1.31

(defn product-iter
  [term a next b]
  (if (> a b)
    1
    (* (term a)
       (product-iter term (next a) next b))))

(defn product-recur
  [term a next b]
  (loop [a a
         acc 1]
    (if (> a b) acc
        (recur (next a) (* acc (term a))))))

(defn product
  [term a next b]
  (reduce * 1
          (map term (take-while #(<= % b)
                                (iterate next a)))))

;;; Exercise 1.32

(defn accumulate-recur
  [combiner null-value term a next b]
  (loop [a a
         acc null-value]
    (if (> a b) acc
        (recur (next a) (combiner acc (term a))))))

(defn accumulate-iter
  [combiner null-value term a next b]
  (if (> a b) null-value
      (combiner (term a)
                (accumulate-iter combiner null-value term (next a) next b))))

(defn sum
  [term a next b]
  (accumulate-iter + 0 term a next b))

(defn product
  [term a next b]
  (accumulate-recur * 1 term a next b))

;;; Exercise 1.33

(defn filtered-accumulate
  [pred combiner null-value term a next b]
  (loop [a a
         acc null-value]
    (if (> a b) acc
        (recur (next a)
               (if (pred a) (combiner acc (term a)) acc)))))

(defn sum-squares-primes
  [a b]
  (filtered-accumulate prime? + 0 square a inc b))

(defn product-prime-n
  [n]
  (filtered-accumulate #(= (.gcd % n) 1)
              * 0 identity 1 inc (dec n)))

;;; Exercise 1.35

(defn fixed-point
  [f first-guess]
  (letfn [(close-enough? [v1 v2]
            (< (Math/abs (- v1 v2)) 0.000001))
          (try-it [guess]
            (let [next (f guess)]
              (if (close-enough? guess next)
                next
                (try-it next))))]
    (try-it first-guess)))

(def phi (fixed-point #(+ 1 (/ 1 %)) 1.0))

;;; Exercise 1.36

(defn fixed-point
  [f first-guess]
  (letfn [(close-enough? [v1 v2]
            (< (Math/abs (- v1 v2)) 0.000001))
          (try-it [guess]
            (println "Look at this ->> " guess)
            (let [next (f guess)]
              (if (close-enough? guess next)
                next
                (try-it next))))]
    (try-it first-guess)))

(defn no-dampening
  [guess]
  (println "No dampening")
  (fixed-point #(/ (Math/log 1000)
                   (Math/log %)) guess))

(defn dampening
  [guess]
  (println "With dampening")
  (fixed-point #(/ (+ %
                      (/ (Math/log 1000)
                         (Math/log %)))
                   2) guess))

;;; Exercise 1.37

(defn cont-frac
  [n d k]
  (letfn [(help [i]
            (if (= i k) (/ (n i) (d i))
                (/ (n i)
                   (+ (d i)
                      (help (inc i))))))]
    (help 1)))

(defn cont-frac
  [n d k]
  (loop [k k
         acc 0]
    (if (< k 1) acc
        (recur (dec k) (/ (n k) (+ (d k) acc))))))

;;; Exercise 1.38

(defn euler
  [i]
  (let [i (dec i)
        idx (mod i 3)]
    (cond (= idx 0) 1
          (= idx 2) 1
          (= idx 1) (* (/ (+ i 2) 3) 2))))

(+ (cont-frac (fn [i] 1.0) euler 90) 2)

;;; Exercise 1.39

(defn tan-cf
  [x k]
  (cont-frac #(if (> % 1) (* -1 (square x)) x)
             #(- (* % 2) 1)
             k))

;;; Exercise 1.40

(defn deriv
  [g]
  (fn [x]
    (/ (- (g (+ x 0.00001)) (g x))
       0.00001)))

(defn newton-transform
  [g]
  (fn [x]
    (- x (/ (g x) ((deriv g) x)))))

(defn newtons-method
  [g guess]
  (fixed-point (newton-transform g) guess))

(defn cubic
  [a b c]
  (fn [x]
    (+ (* x x x)
       (* a x x)
       (* b x)
       c)))

(< ((cubic 1 2 3) (newtons-method (cubic 1 2 3) 1.0))
   0.00001)

;;; Exercise 1.41

(defn double-f
  [f]
  (fn [x]
    (f (f x))))

(((double-f (double-f double-f)) inc) 5)

;;; Exercise 1.42

(defn compose
  [f g]
  (fn [x]
    (f (g x))))

((compose square inc) 6)

;;; Exercise 1.43

(defn repeated
  [f n]
  (if (= n 1) f
      (compose f (repeated f (dec n)))))

(defn repeated
  [f n]
  (fn [x]
    (last (take (inc n) (iterate f x)))))

((repeated square 2) 5)

;;; Exercise 1.44

(defn smooth
  [f]
  (fn [x]
    (/ (+ (f (- x 0.00001))
          (f x)
          (f (+ x 0.00001)))
       3)))

(defn n-fold-smooth
  [f n]
  (repeated (smooth f) n))

;;; Exercise 1.45

(defn average-damp
  [f]
  (fn [x] (average x (f x))))

(defn nth-root
  [n x]
  (fixed-point ((repeated average-damp
                          (Math/ceil (/ n 2.0)))
                (fn [y] (/ x (Math/pow y (dec n)))))
               1.0))

;;; Exercise 1.46

(defn iterative-improve
  [good-enough? improve]
  (fn [guess]
    (loop [previous-guess guess
           current-guess (improve guess)]
      (if (good-enough? previous-guess) current-guess
          (recur current-guess (improve current-guess))))))

(defn sqrt
  [x]
  ((iterative-improve #(< (Math/abs (- (square %) x)) 0.0001)
                      #(/ (+ % (/ x %)) 2))
   x))

(defn fixed-point
  [f guess]
  ((iterative-improve #(< (Math/abs (- (f %) %)) 0.0001)
                      #(f %))
   guess))
