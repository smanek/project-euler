(defmacro while (expression &body body)
  `(tagbody
    start (if (not ,expression) (go end))
      ,@body
      (go start)
    end))

(defun fibonacci (n)
  "Compute the n'th Fibonacci number."
  (if (or (zerop n) (= n 1))
      1
      (+ (fibonacci (- n 1)) (fibonacci (- n 2)))))

(defun squash (statement)
  "returns all atoms in statement as an un-nested list"
  (cond 
   ((null statement) nil)
   ((atom statement) (list statement))
   ('t (append (squash (first statement))
               (squash (rest statement))))))

(defun fact (n &optional (acc 1))
  (if (<= n 1)
      acc
     (fact (- n 1) (* acc n))))

(defun num-sublists-i (lis)
  (let ((result 0))
    (dolist (next lis result)
      (if (listp next) 
	  (setf result (1+ result))))))

(defun rec_enum (lis)
(let ((result NIL))
  (dolist (next lis result)
    (if (atom next)
	(setq result (append result (cons (princ next) NIL)))
	(setq result (append result (rec_enum next)))))))

(defun mymax (nums)                     
  (cond ((= (length nums) 1) (car nums))
	((> (car nums) (cadr nums))     
	 (mymax (cons (car nums) 
		      (cddr nums))))    
	(t (mymax (cdr nums)))))        

(defun arraydem (size)
  (let* ((a (ceiling (sqrt size)))
	 (myArr (make-array `(,a ,a)))
	 (r 0) 
	 (c 0))
    (dotimes (count size)
      (setf (aref myArr r c) (+ 1 count))
      (setf c (+ c 1))
      (if (= c a)
          (setf c 0 r (+ 1 r))))
    myArr))

(defun prompt-read (prompt)
  (format *query-io* "~a: " prompt)
  (force-output *query-io*)
  (read-line *query-io*))

(defun palinp (s)
  (cond ((atom s) t)
	('t (and 
	     (equal (first s) (first (last s))) 
	     (palinp (rest (butlast s)))))))

(defun avgrandom (n max &optional (cur 0) (dn 0))
  (cond ((eq n 0) (float (/ cur dn)))
	('t (avgrandom (decf n) max (+ cur (random max)) (incf dn)))))

(defun map-roots (count)
  (reverse (mapcar #'sqrt 
		   ((lambda (c) 
		      (let ((result '())) 
			(dotimes (i c result) (push i result))))
		    count))))

(defun naive-primep (num)
  (do ((i 2 (1+ i)))
      ((> i (floor (sqrt num))))
    (if (equal (mod num i) 0)
	(return-from naive-primep nil)))
  t)

(defun mod-exp-naive (b e m)
  "Computes a^b mod c slowly"
  (mod (expt b e) m))

(defun mod-exp (b e m &optional (c 1) (ep 0))
  "Computes b^e mod m considerably quicker"
  (declare (optimize (speed 3) (safety 0))) 
  (setf ep (+ 1 ep))
  (setf c (mod (* b c) m))
  (if (< ep e)
      (mod-exp b e m c ep)
      c))

(defun mod-exp-ue (b e m)
  (declare (optimize (speed 3) (safety 0)))
  (let ((result 1))
    (while (> e 0)
      (when (= (logand e 1) 1)
	(setf result (mod (* result b) m)))
      (setf e (ash e -1))
      (setf b (mod (expt b 2) m)))
    result))

(defun fermat-primep (num &optional (k 30))
  (declare (optimize (speed 3) (safety 0)))
  (if (or (< num 2) (not (typep num 'integer)))
      (return-from fermat-primep nil))
  (dotimes (i (- k 1))
    (let ((r (+ 1  (random (- num 1)))))
      (if (not (equal (mod-exp-ue r (- num 1) num) 1) )
	  (return-from fermat-primep NIL))))
  't)

(defun benchmark (iter fn &rest args)
  (time (dotimes (i iter) 
	  (apply fn args))))

(defun foldl (fn ls &optional (cur '() cur-set))
  (cond ((not (null cur-set)) 
	 (cond ((> (length ls) 0) (foldl fn (cdr ls) 
					     (apply fn (list cur (car ls)))))
	       ('t cur)))
	('t (foldl fn (cddr ls) (apply fn (list (car ls) (cadr ls)))))))

(defun rewrite-remove-if (fn ls)
  (if (null ls)
      nil
      (if (funcall fn (car ls))
	  (rewrite-remove-if fn (cdr ls))
	  (cons (car ls) (rewrite-remove-if fn (cdr ls))))))

(let ((x 0))
  (defun lexical-scoping-total (y)
    (incf x y)))

(defun make-circular-list ()
  (setf *print-circle* 't)
  (let ((ls (copy-list '(a b c))))
    (setf (cdr (last ls)) ls)
    ls))

(defun euler-one (n)
  (let ((sum 0))
    (dotimes (i n)
      (when (or 
	     (equal (mod i 3) 0) 
	     (equal (mod i 5) 0))
	(setf sum (+ i sum))))
    sum))

(defun euler-three (n)
  (let ((factors nil))
    (dotimes (i (isqrt n))
      (when (and (eq 0 (mod n (+ 1 i)))
		 (fermat-primep (+ 1 i)) )
	(setf factors (cons (+ 1 i) factors))))
     factors))

(defun prime-factorization (n)
  (assert (typep n 'integer))
  (assert (> n 0))
  (let ((factors nil))
    (loop for i from 1 upto (isqrt n)
	do (when (= 0 (mod n i))
	     (when (fermat-primep i) (setf factors (cons i factors)))
	     (when (fermat-primep (/ n i)) (setf factors (cons (/ n i) factors))))
	 finally (return factors))))

(defun prime-factorization-mult (n)
  (cond ((= n 1) nil)
	((fermat-primep n) (list n))
	('t (loop for i from 2 until (= 0 (mod n i)) finally (return (append (prime-factorization-mult i) (prime-factorization-mult (/ n i))))))))

(defun euler-eight ()
  (let ((numbers (mapcar #'(lambda (x) (parse-integer (string x))) (concatenate 'list "7316717653133062491922511967442657474235534919493496983520312774506326239578318016984801869478851843858615607891129494954595017379583319528532088055111254069874715852386305071569329096329522744304355766896648950445244523161731856403098711121722383113622298934233803081353362766142828064444866452387493035890729629049156044077239071381051585930796086670172427121883998797908792274921901699720888093776657273330010533678812202354218097512545405947522435258490771167055601360483958644670632441572215539753697817977846174064955149290862569321978468622482839722413756570560574902614079729686524145351004748216637048440319989000889524345065854122758866688116427171479924442928230863465674813919123162824586178664583591245665294765456828489128831426076900422421902267105562632111110937054421750694165896040807198403850962455444362981230987879927244284909188845801561660979191338754992005240636899125607176060588611646710940507754100225698315520005593572972571636269561882670428252483600823257530420752963450"))))
    (labels ((rec-max-seq (lst max)
	       (cond ((< (length lst) 5) max) 
		     ((> (* (first lst) (second lst) (third lst) (fourth lst) (fifth lst)) max)
		      (rec-max-seq (cdr lst) (* (first lst) (second lst) (third lst) (fourth lst) (fifth lst))))
		     ('t (rec-max-seq (cdr lst) max)))))
      (rec-max-seq numbers 0))))

(defun all-factors (n)
  (let ((results nil))
    (dotimes (i (isqrt n))
      (when (= (mod n (+ i 1)) 0)
	(setf results (cons (+ 1 i) results))
	(setf results (cons (/ n (+ 1 i)) results))))
    results))


(defun euler-twelve (&optional (start (list 0)))
  (cond ((> (length (all-factors (apply #'+ start))) 500) (apply #'+ start))
	('t (euler-twelve (cons (length start) start)))))

(defun euler-seventeen ()
  (let ((num-words nil))
    (dotimes (i 1000)
      (setf num-words (concatenate 'string num-words (format nil "~r" (+ 1 i)))))
    (print num-words)
    (- (length num-words) (count (char " " 0) num-words) (count #\- num-words))))

(defun euler-twenty ()
  (apply #'+ 
	 (mapcar 
	  #'(lambda (x) 
	      (parse-integer (string x))) 
	  (concatenate 'list (write-to-string (fact 100))))))


(defun euler-twentyseven ()
  (flet ((quad-consec-prime (a b)
	   (let ((consec-primes 0))
	     (while (fermat-primep (+ (expt consec-primes 2) (* a consec-primes) b))
	       (incf consec-primes))
	     consec-primes)))
    (let ((max 0)
	  (result nil))
      (dotimes (i 1999)
	(format t "New A of ~A~%" (- i 999))
	(dotimes (j 1999)
	  (let* ((a (- i 999))
		(b (- j 999))
		(res (quad-consec-prime a b)))
	    (if (> res max)
		(progn 
		  (setf max res)
		  (setf result (list a b))
		  (format t "New Best answer:~%A: ~A~tB: ~A~TConsecutive Sequence: ~A~TProduct: ~A~%~%" a b res (* a b)))))))
      (format t "Final answerA: ~A~tB: ~A~TConsecutive Sequence: ~A~TProduct: ~A~%" (car result) (cadr result) max (* (car result) (cadr result))))))


(defun permutations (bag)
  "Return a list of all the permutations of the input."
  (if (null bag) 
      '(())
      (mapcan #'(lambda (e)
                  (mapcar #'(lambda (p) (cons e p))
                          (permutations
			   (remove e bag :count 1))))
              bag)))

(defun permutations-number (n)
  (assert (typep n 'integer))
  (mapcar #'(lambda (num-list) (parse-integer (concatenate 'string num-list))) 
	  (permutations (concatenate 'list (write-to-string n)))))

(defun cycles-number (n)
  (assert (typep n 'integer))
  (setf *print-circle* 't)
  (let* ((lst (concatenate 'list (write-to-string n)))
	 (lngt (length lst))
	 (res nil))
    (setf (cdr (last lst)) lst)
    (dotimes (i lngt)
      (setf res (cons (parse-integer (concatenate 'string (subseq lst i (+ i lngt)))) res)))
    res))

(defun euler-thirtyfive (n)
  (declare (optimize (speed 3) (safety 0)))
  (let ((count 0))
    (dotimes (i n)
      (when (= 0 (mod i 1000)) (format t "---Now at ~A---~%" i))
      (let ((lst-ints (concatenate 'list (write-to-string i))))
	(if (and (> (length lst-ints) 1) (or (member #\2 lst-ints) (member #\4 lst-ints) (member #\6 lst-ints) (member #\8 lst-ints) (member #\0 lst-ints) (member #\5 lst-ints)))
	    nil
	    (when (every #'fermat-primep (cycles-number i))
	      (format t "Found one at ~A~%" i)
	      (incf count)))))
    count))

(defun euler-thirtyfive-efficient (n)
  (declare (optimize (speed 3) (safety 0)))
  (let ((primes (make-hash-table))
	(res 0))
    (dotimes (i n)
      (when (fermat-primep i 15)
;;	(format t "Found prime ~A~%" i)
	(setf (gethash i primes) t)))
    (format t "Computed All Primes < ~A~%" n)
    (dotimes (i n)
      (when (every #'(lambda (x) (gethash x primes)) (permutations-number i))
	(when (= 0 (mod i 1000)) (format t "---Now at ~A---~%" i))
	(format t "Found one at ~A~%" i)
	(incf res)))
    ;;    (count T (mapcar #'(lambda (n) (every #'(lambda (p) (gethash p primes)) (permutations-number n))) primes))  ;This line segfaults?!
    res))
 
(defun get-primes (n)
  "The first n primes"
  (let ((primes nil)
	(i 2))
    (while (< (length primes) n)
      (when (fermat-primep i)
	(setf primes (cons i primes)))
      (incf i))
    primes))

(defun get-primes-below-naive (n)
  (let ((primes nil)
	(i 2))
    (while (< i n)
      (when (naive-primep i)
	(setf primes (cons i primes)))
      (incf i))
    primes))

(defun euler-seven (nth)
  (loop with n = 1 with count = 0 
     while (not (= count nth)) 
     do (incf n) 
     when (naive-primep n) 
     do (incf count) 
     finally (return n)))

(defun euler-two (n)
  (let ((fib-seq (list 2 1)))
    (while (< (+ (cadr fib-seq) (car fib-seq)) n)
      (setf fib-seq (cons (+ (car fib-seq) (cadr fib-seq)) fib-seq)))
    (apply #'+ (mapcar #'(lambda (n) (if (evenp n) n 0)) fib-seq))))

(defun euler-six (n)
  (labels ((sum-squares (lst)
	     (cond ((null (cdr lst)) (expt (car lst) 2))
		    ('t (+ (expt (car lst) 2) (sum-squares (cdr lst))))))
	   (square-sums (lst)
	     (expt (apply #'+ lst) 2)))
    (let ((operating nil))
      (dotimes (i n) (setf operating (cons (+ 1 i) operating)))
      (- (square-sums operating) (sum-squares operating)))))

(defun gen-list-ints (n)
  (let ((operating nil))
    (dotimes (i n) (setf operating (cons (+ 1 i) operating)))
    (reverse operating)))

(defun unique-elts (lst)
  "Returns a list of all the unique elements in lst. Possibly use hashtables in future for scaling"
  (let ((res nil))
    (dolist (i lst)
      (when (not (member i res)) (setf res (cons i res))))
    res))

(defun euler-five (n)
  "What is the smallest number that is evenly divisible by all of the numbers from 1 to 20?"
  (let ((res nil)
	(denom (gen-list-ints n))
	(count 1))
    (while (null res)
      (when (every #'(lambda (n) (= 0 (mod count n))) denom) (setf res count))
      (incf count))
    res))

(defun euler-four ()
"Find the largest palindrome made from the product of two 3-digit num1bers."
  (loop for i from 100 upto 999 maximizing
       (loop for j from 100 upto 999
	    maximizing (if (palinp (concatenate 'list (write-to-string (* i j)))) 
			   (* i j)
			   -1) into max
	    finally (return max)) into max
       finally (return max)))

(defun euler-nine ()
  "Find a*b*c when a + b + c = 1000 and a^2+b^2=c^2"
  (dotimes (m (isqrt 1000))
    (dotimes (n (isqrt 1000))
      (let ((a (- (expt m 2) (expt n 2)))
	    (b (* 2 m n))
	    (c (+ (expt m 2) (expt n 2))))
	(when (= (+ a b c) 1000) (return-from euler-nine (* a b c)))))))

(defun euler-twentyfive ()
  "What is the first term in the Fibonacci sequence to contain 1000 digits?"
  (let ((fib-seq (list 2 1)))
    (while (< (length (write-to-string (car fib-seq))) 1000)
      (setf fib-seq (cons (+ (car fib-seq) (cadr fib-seq)) fib-seq)))
    (length fib-seq)))

(defun euler-fortyone ()
  (let ((perms (permutations-number 1234567))
	(primes nil))
    (dolist (i perms)
      (when (fermat-primep i) (setf primes (cons i primes))))
    (car (sort primes #'>))))

(defun euler-eleven ()
  (let ((arrn (make-array '(20 20) 
			  :element-type 'integer 
			  :initial-contents '((08 02 22 97 38 15 00 40 00 75 04 05 07 78 52 12 50 77 91 08)
					      (49 49 99 40 17 81 18 57 60 87 17 40 98 43 69 48 04 56 62 00)
					      (81 49 31 73 55 79 14 29 93 71 40 67 53 88 30 03 49 13 36 65)
					      (52 70 95 23 04 60 11 42 69 24 68 56 01 32 56 71 37 02 36 91)
					      (22 31 16 71 51 67 63 89 41 92 36 54 22 40 40 28 66 33 13 80)
					      (24 47 32 60 99 03 45 02 44 75 33 53 78 36 84 20 35 17 12 50)
					      (32 98 81 28 64 23 67 10 26 38 40 67 59 54 70 66 18 38 64 70)
					      (67 26 20 68 02 62 12 20 95 63 94 39 63 08 40 91 66 49 94 21)
					      (24 55 58 05 66 73 99 26 97 17 78 78 96 83 14 88 34 89 63 72)
					      (21 36 23 09 75 00 76 44 20 45 35 14 00 61 33 97 34 31 33 95)
					      (78 17 53 28 22 75 31 67 15 94 03 80 04 62 16 14 09 53 56 92)
					      (16 39 05 42 96 35 31 47 55 58 88 24 00 17 54 24 36 29 85 57)
					      (86 56 00 48 35 71 89 07 05 44 44 37 44 60 21 58 51 54 17 58)
					      (19 80 81 68 05 94 47 69 28 73 92 13 86 52 17 77 04 89 55 40)
					      (04 52 08 83 97 35 99 16 07 97 57 32 16 26 26 79 33 27 98 66)
					      (88 36 68 87 57 62 20 72 03 46 33 67 46 55 12 32 63 93 53 69)
					      (04 42 16 73 38 25 39 11 24 94 72 18 08 46 29 32 40 62 76 36)
					      (20 69 36 41 72 30 23 88 34 62 99 69 82 67 59 85 74 04 36 16)
					      (20 73 35 29 78 31 90 01 74 31 49 71 48 86 81 16 23 57 05 54)
					      (01 70 54 71 83 51 54 69 16 92 33 48 61 43 52 01 89 19 67 48))))
	(max 0))
    (loop for i from 0 upto 16 do 
	 (loop for j from 0 upto 19 do
	      (let ((vert (* (aref arrn j i) (aref arrn j (+ 1 i)) (aref arrn j (+ 2 i)) (aref arrn j (+ 3 i))))
		    (horiz (* (aref arrn i j) (aref arrn (+ 1 i) j) (aref arrn (+ 2 i) j) (aref arrn (+ 3 i) j))))
		(when (< max vert) (setf max vert) (format t "Found a new max product (vert) of ~A~%" vert))
		(when (< max horiz) (setf max horiz) (format t "Found a new max product (horiz) of ~A~%" horiz)))))
    (loop for i from 0 upto 16 do
	 (loop for j from 0 upto 16 do
	      (let ((downright-diag (* (aref arrn j i) (aref arrn (+ 1 j) (+ 1 i)) (aref arrn (+ 2 j) (+ 2 i)) (aref arrn (+ 3 j) (+ 3 i)))))
		(when (< max downright-diag) (setf max downright-diag) (format t "Found a new max product (downright-diag) of ~A~%" downright-diag)))))
    (loop for i from 19 downto 3 do
	 (loop for j from 19 downto 3 do
	      (let ((downleft-diag (* (aref arrn j i) (aref arrn (- j 1) (- i 1)) (aref arrn (- j 2) (- i 2)) (aref arrn (- j 3) (- i 3)))))
		(when (< max downleft-diag) (setf max downleft-diag) (format t "Found a new max product (downleft-diag) of ~A~%" downleft-diag)))))
    (format t "~%~%The max I saw was ~A~%~%" max)))



(defun gen-efourteen-iter-seq (n &optional (lst nil))
  (assert (typep n 'integer))
  (cond ((< n 1) (list n))
	((= n 1) (reverse (cons 1 lst)))
	((evenp n) (gen-efourteen-iter-seq (/ n 2) (cons n lst)))
	('t (gen-efourteen-iter-seq (+ (* 3 n) 1) (cons n lst)))))

(defun euler-fourteen (n)
;;Answer 837799
  (let ((seen-hash (make-hash-table))
	(max '(0 . -1)))
    (loop for i from n downto 1 do
	 (progn  
	   (when (= 0 (mod i 10000)) (format t "---Now at ~A---~%" i))
	   (if (gethash i seen-hash) 
	       nil
	       (let* ((seq (gen-efourteen-iter-seq i))
		      (len (length seq)))
		 (when (> len (cdr max))
		   (setf max (cons i len))
		   (format t "New Best! ~A generates a sequence of ~A~%" i len))
		 (dolist (j seq)
		   (setf (gethash j seen-hash) 't))))))
    (format t "~%~%~A Generated a sequence of length ~A~%~%" (car max) (cdr max))))

(defun amic-pair (n)
  "Returns the sum of all proper divisors of n"
  (- (apply #'+ (all-factors n)) n))

(defun euler-twentyone ()
  (loop for i from 2 upto 10000 when (and (= i (amic-pair (amic-pair i))) (not (= (amic-pair i) i)))
     collect i into res finally (return res)))

(defun euler-thirty ()
  (loop for i from 10 upto 1000000 when 
       (= i (apply #'+ (mapcar #'(lambda (n) (expt n 5)) 
			       (mapcar #'(lambda (n) (parse-integer (string n))) (concatenate 'list (write-to-string i))))))
     collecting i into res finally (return (apply #'+ res))))

(defun euler-thirtysix ()
  (loop for i from 1 upto 1000000 when (every #'palinp (list (concatenate 'list (write-to-string i)) (concatenate 'list (write-to-string i :base 2))))
       collecting i into res finally (return res)))

(defun euler-thirtyfour ()
  (loop for i from 4 upto 2000000 when 
       (= i (apply #'+ (mapcar #'(lambda (n) (fact n)) 
			       (mapcar #'(lambda (n) (parse-integer (string n))) (concatenate 'list (write-to-string i))))))
     collecting i into res finally (return (apply #'+ res))))

(defun euler-twentynine ()
  (let ((res nil))
    (loop for a from 2 upto 100 do
	 (loop for b from 2 upto 100 do (setf res (cons (expt a b) res))))
    (length (unique-elts res))))

(defun euler-forty ()
  "Answer 210"
  (let ((res 1)
	(len 1)
	(count 1))
    (while (<= len 1000010)
      ;;      (when ( = 0 (mod len 100)) (format t "--Now at length ~A and count ~A--~%" len count))
      (dolist (i (concatenate 'list (write-to-string count)))
	(when (member len '(1 10 100 1000 10000 100000 1000000))
	      (format t "Digit: ~A~TValue: ~A~%" len i)
	      (setf res (* res (parse-integer (string i)))))
	(incf len))
      (incf count))
    res))

(defun euler-fiftytwo ()
  "Answer is 142857"
  (let ((res nil)
	(count 1))
    (while (not res)
      (let ((twox  (mapcar #'(lambda (n) (parse-integer (string n))) (concatenate 'list (write-to-string (* count 2))))))
	(when (every #'(lambda (n) (null (or (set-difference twox n) (set-difference n twox)))) 
		     (mapcar #'(lambda (n) (mapcar #'(lambda (x) (parse-integer (string x))) n))													(mapcar #'(lambda (n) (concatenate 'list  (write-to-string n))) (list (* 3 count) (* 4 count)  (* 5 count)  (* 6 count)))))
	  (setf res count)))
      (incf count))
    res))

(defun read-csv-stream (stream &key (state 0) (working-result nil) (results nil) (line nil)) 
  "A (sort-of) finite state machine to properly parse a csv file. Technically, it's a bit too leniant 
with nominally malformed files and will attempt to do the right thing instead of just failing"
;;State 0 is normal unquoted state, in which we're just naively reading non-special characters
;;State 1 is quoted state. We're reading all characters
;;State 2 is after a second quote has been encountered. A third quote will be interpreted as a literal quote
  (let ((cur-char (read-char stream nil)))
    (cond ((null cur-char) 
           (when (or line working-result) ;;Catch in case csv doesn't have a trailing newline
                             (setf results (cons (reverse (cons working-result line)) results))) 
           (reverse results))
          ((and (= state 0) 
                (equal cur-char #\")) (read-csv-stream stream :state 1 :results results :line line))
          ((and (= state 0) (equal cur-char #\,)) 
           (read-csv-stream stream :state 0 :results results :line (cons working-result line)))
          ((and (= state 0) (equal cur-char #\Newline)) 
           (read-csv-stream stream :state 0 :results (cons (reverse (cons working-result line)) results)))
          ((= state 0) 
           (read-csv-stream stream :state 0 :results results :working-result
                            (concatenate 'string working-result (string cur-char)) :line line))       
          ((and (= state 1) (equal cur-char #\")) 
           (read-csv-stream stream :state 2 :results results :line line :working-result working-result))
          ((= state 1) 
           (read-csv-stream stream :state 1 :results results :line line :working-result 
                            (concatenate 'string working-result (string cur-char))))        
          ((and (= state 2) (equal cur-char #\Newline)) 
           (read-csv-stream stream :state 0 :results (cons (reverse (cons working-result line)) results)))
          ((and (= state 2) (equal cur-char #\,)) 
           (read-csv-stream stream :state 0 :results results :line (cons working-result line)))
          ((and (= state 2) (equal cur-char #\")) 
           (read-csv-stream stream :state 1 :results results :line line :working-result 
                            (concatenate 'string working-result (string cur-char))))
          ((= state 2) 
           (read-csv-stream stream :state 2 :results results :line line))
          ('t 
           (format t "Slipped through the FSM. This should be impossible. Cur-char is ~A state is ~A~%" cur-char state)))))

(defun euler-twentytwo ()
  (let ((names (sort (car (with-open-file (str "/Users/smanek/Desktop/Code/Lisp/names.txt") (read-csv-stream str))) #'string<))
	(count 1)
	(res 0)
	(letter-mappings '((#\A . 1) (#\B . 2) (#\C . 3) (#\D . 4)(#\E . 5)(#\F . 6)(#\G . 7)(#\H . 8)(#\I . 9)(#\J . 10)(#\K . 11)(#\L . 12)(#\M . 13)(#\N . 14) 	
			   (#\O . 15)(#\P . 16)(#\Q . 17)(#\R . 18)(#\S . 19)(#\T . 20)(#\U . 21)(#\V . 22)(#\W . 23)(#\X . 24)(#\Y . 25)(#\Z . 26))))
    (dolist (i names)
      (setf res (+ res (* count (apply #'+ (mapcar #'(lambda (n) (cdr (assoc n letter-mappings))) (concatenate 'list i))))))
      (incf count))
    res))

(defun all-proper-factors (n)
  (loop for i from 2 upto (isqrt n) when (= 0 (mod n i)) collect i into factors 
     and when (not (= i (/ n i))) collect (/ n i) into factors 
     finally (return (cons 1 factors))))

(defun abundant-p (n)
  (if (< n (apply #'+ (all-proper-factors n)))
      t
      nil))

(defun euler-twentythree ()
  (let ((abundant-sums (make-hash-table)))
    (loop for i from 1 upto 28123 when (abundant-p i) collecting i into
       abundants finally (loop for j from 0 upto (- (length abundants)
						    1) do
			      (loop for k from j upto (- (length abundants) 1) collecting (+ (elt abundants j) (elt abundants k)) into sub-sum 
				 finally (progn 
					   (when (= 0 (mod j 100)) (format t "Finished for ~A out of ~A~%" j (- (length abundants) 1)))
					   (dolist (l sub-sum) (setf (gethash l abundant-sums) 't))))))
    (loop for i from 1 upto 28123 when (not (gethash i abundant-sums)) collecting i into results finally (return (apply #'+ results)))))

(defun day-of-week (day month year)
    "Returns the day of the week as an integer.
Monday is 0."
    (nth-value
     6
     (decode-universal-time
      (encode-universal-time 0 0 0 day month year 0)
      0)))

(defun days-in-month (year month)
  (cond ((or (= month 9) (= month 10) (= month 4) (= month 6)) 30)
	((= month 2) (if (= 0 (mod year 4)) 29 28))
	('t 31)))

(defun euler-nineteen ()
  (let ((count 0))
    (loop for year from 1901 upto 2000 do
	 (loop for month from 1 upto 12 do
	      (loop for day from 1 upto (days-in-month year month) when (and (= 1 day) 
									     (= 0 (day-of-week day month year))) do (progn (format t "~A-~A-~A~%" year month day) (incf count)))))
    count))

(defun euler-fourtytwo ()
  (let ((words (car (with-open-file (str "/Users/smanek/Desktop/Code/Lisp/words.txt") (read-csv-stream str))))
	(count 0)
	(letter-mappings '((#\A . 1) (#\B . 2) (#\C . 3) (#\D . 4)(#\E . 5)(#\F . 6)(#\G . 7)(#\H . 8)(#\I . 9)(#\J . 10)(#\K . 11)(#\L . 12)(#\M . 13)(#\N . 14) 	
			   (#\O . 15)(#\P . 16)(#\Q . 17)(#\R . 18)(#\S . 19)(#\T . 20)(#\U . 21)(#\V . 22)(#\W . 23)(#\X . 24)(#\Y . 25)(#\Z . 26)))
	(triangle-numbers (loop for i from 1 upto 100 collect (* (/ 1 2) i (+ 1 i)) into results finally (return results))))
    (setf words (mapcar #'(lambda (i) (apply #'+ (mapcar #'(lambda (n) (cdr (assoc n letter-mappings))) (concatenate 'list i)))) words))
    (dolist (i words)
      (when (member i triangle-numbers)
	(incf count)))
    count))

(defun combination-count (n r)
  (/ (apply #'* (loop for i from n downto (+ 1 r) collect i into res finally (return res))) (fact (- n r))))

(defun euler-fiftythree ()
  (let ((count 0)) 
    (loop for n from 100 downto 23 do
	 (progn (format t "On ~A~%" n)
		(loop for r from n downto 1 when (< 1000000 (combination-count n r)) do (incf count))))
    count))

(defun triangle-p (n)
  (let ((sol-o (/ (+ -1 (sqrt (+ 1 (* 8 n)))) 2))
	(sol-t (/ (- -1 (sqrt (+ 1 (* 8 n)))) 2)))
    (when (and 
           (multiple-value-bind (i dec) (floor sol-o) (= 0 dec)) 
           (< 0 sol-o)) 
      (return-from triangle-p sol-o))
    (when (and 
           (multiple-value-bind (i dec) (floor sol-t) (= 0 dec)) 
           (< 0 sol-t)) (return-from triangle-p sol-t))
    nil))

(defun pentagonal-p (n)
  (let ((sol-o (/ (+ 1 (sqrt (+ 1 (* 24 n)))) 6))
	(sol-t (/ (- 1 (sqrt (+ 1 (* 24 n)))) 6)))
    (if (or (and 
             (multiple-value-bind (i dec) (floor sol-o) (= 0 dec)) 
             (< 0 sol-o))
	    (and 
             (multiple-value-bind (i dec) (floor sol-t) (= 0 dec)) 
             (< 0 sol-t)))
	t
	nil)))

(defun hexagonal-p (n)
  (let ((sol-o (/ (+ 1 (sqrt (+ 1 (* 8 n)))) 4))
	(sol-t (/ (- 1 (sqrt (+ 1 (* 8 n)))) 4)))
    (if (or (and (multiple-value-bind (i dec) (floor sol-o) (= 0 dec)) (< 0 sol-o))
	    (and (multiple-value-bind (i dec) (floor sol-t) (= 0 dec)) (< 0 sol-t)))
	t
	nil)))

(defun euler-fortyfive ()
  (loop for i from 40756 
     when (and (triangle-p i) (hexagonal-p i) (pentagonal-p i)) 
     do (return i)))

(defun euler-thirtythree ()
;;Answer is 100. Four numbers are (/ 49 98) (/ 19 95) (/ 26 65) (/ 16 64)
  (let ((res nil))
    (loop for denom from 11 upto 99 when (not (= 0 (mod denom 10))) 
       do (loop for num from 11 upto (- denom 1) when (not (= 0 (mod num 10))) 
	     do (cond ((= (parse-integer (subseq (write-to-string num) 0 1)) (parse-integer (subseq (write-to-string denom) 1 2)))
		       (when (= (/ num denom) (/ (parse-integer (subseq (write-to-string num) 1 2)) (parse-integer (subseq (write-to-string denom) 0 1))))
			 (setf res (cons (format nil "~A / ~A" num denom) res))))
		      ((= (parse-integer (subseq (write-to-string num) 1 2)) (parse-integer (subseq (write-to-string denom) 0 1)))
		       (when (= (/ num denom) (/ (parse-integer (subseq (write-to-string num) 0 1)) (parse-integer (subseq (write-to-string denom) 1 2))))
			 (setf res (cons (/ num denom) res)))))))
    (apply #'* res)))

(defun truncatable-prime (n &optional (direction 2))
  "If direction is 0 it means from the left, 1 means right, none means both"
  (cond ((null n) 't)
	((= direction 0) (if (and (fermat-primep n) (truncatable-prime (handler-case (parse-integer (write-to-string n) :start 1) (error nil)) 0)) 't nil))
	((= direction 1) (if (and (fermat-primep n) (truncatable-prime (handler-case (parse-integer (write-to-string n) :end (- (length (write-to-string n)) 1)) (error nil)) 1)) 't nil))
	((= direction 2) (if (and (truncatable-prime n 0) (truncatable-prime n 1)) 't nil))))

(defun euler-thirtyseven ()
  (loop for i from 11 when (and (fermat-primep i) (truncatable-prime i)) collect i into res until (= 11 (length res)) finally (return res)))

(defun sum-digits (n)
  (assert (typep n 'integer))
  (apply #'+ (mapcar #'(lambda (digit) (parse-integer (string digit))) (concatenate 'list (write-to-string n)))))

(defun euler-fiftysix ()
  (loop for i from 0 upto 99 maximize 
       (loop for j from 0 upto 99 maximize (sum-digits (expt i j)) into max finally (return max))
       into max finally (return max)))

(defun euler-thirtynine ()
  (let ((hash-results (make-hash-table))
	(max-count 0)
	(max-perimeter 0))
    (loop for a from 1 upto 500 do
	 (loop for b from 1 upto 500 do 
	      (let ((sum (+ a b (sqrt (+ (expt a 2) (expt b 2))))))
	      (if (< sum 1000)
		  (setf (gethash sum hash-results) (+ 1 (or (gethash sum hash-results) 0)))
		  (return)))))
    (loop for k being the hash-key using (hash-value v) of hash-results when (> v max-count) do 
	 (progn 
	   (setf max-count v) (setf max-perimeter k)))
    (format t "The perimeter ~A occurred ~A Times" max-perimeter max-count)
    max-perimeter))

(defun lychrel-p (n &optional (count 0))
  (if (< count 50)
    (let ((next (+ n (parse-integer (reverse (write-to-string n))))))
      (if (palinp (concatenate 'list (write-to-string next)))
	  t
	  (lychrel-p next (+ count 1))))
    nil))

(defun euler-fiftyfive ()
  (loop for i from 1 upto 9999 counting (not (lychrel-p i)) into count-lyc finally (return count-lyc)))

(defun number-chain-at-89 (n hash-seen &optional (seen nil))
  (cond ((= n 1) nil)
	((or (= n 89) (gethash n hash-seen)) (cons n seen))
	('t (number-chain-at-89 (apply #'+ (mapcar #'(lambda (digit) (expt (parse-integer (string digit)) 2)) (concatenate 'list (write-to-string n)))) hash-seen (cons n seen)))))

(defun euler-ninetytwo (n)
  (let ((res-hash (make-hash-table )))
    (loop for i from 1 upto (- n 1) when (null (gethash i res-hash)) do
	 (let ((chain (number-chain-at-89 i res-hash)))
	   (dolist (link chain) 
	     (when (< link n)
	       (setf (gethash link res-hash) t)))))
    res-hash))

(defun euler-sixtythree ()
  (loop for power from 1 upto 1000 append
       (loop for base from 1 with results do 
	    (cond ((= (length (write-to-string (expt base power))) power) (setf results (cons (cons base power) results)))
		  ((> (length (write-to-string (expt base power))) power) (return results)))) into res finally (return res)))

(defun pandigital-p (n)
  (cond ((typep n 'integer) (pandigital-p (write-to-string n)))
	((typep  n 'string) (when (not (= 9 (length n))) (return-from pandigital-p nil)) (let ((list-n (mapcar #'string (concatenate 'list n)))) 
			      (loop for i from 1 upto 9 always (member (write-to-string i) list-n :test #'string=))))))

(defun concan-product (n mult)
  "Pass it a number, and a list of things to multiply by.
For example, (concan-product 2 '(1 2 3)) returs 246"
  (format nil "~{~A~}" (mapcar #'(lambda (m) (* n m)) mult)))

(defun euler-thirtyeight ()
  (let ((max 0))
    (loop for i from 1 upto 50000 do
	 (loop for j from 2 upto 9 collecting j into res 
	    do (let ((concp (parse-integer (concan-product i (cons 1 res)))))
		 (when (and (pandigital-p concp) (> concp max))
		   (format t "Found new high at ~A~%" concp)
		   (setf max concp)))))
    max))

(defun compressed-prime-factors (n)
  "This functions returns the compressed prime factors of n.
For example, c-p-f(8) should return ((2 . 3)), because it's prime factors are 2^3"
  (let ((raw-fact (prime-factorization-mult n))
	(res nil))
    (dolist (i raw-fact) 
      (if (cdr (assoc i res))
	  (setf (cdr (assoc i res)) (+ 1 (cdr (assoc i res))))
	  (setf res (acons i 1 res))))
    res))


(defun euler-fortyseven ()
  (loop for i from 2 do
       (let ((a (compressed-prime-factors i))
	     (b (compressed-prime-factors (+ 1 i)))
	     (c (compressed-prime-factors (+ 2 i)))
	     (d (compressed-prime-factors (+ 3 i))))
	 (when (and (every #'(lambda (n) (= 4 (length n))) (list a b c d))
		    (= 16 (length (unique-elts (append a b c d))))) ;This is slow, but working, code to gurantee the prime factors are distinct. too lazy to write better now
	   (return-from euler-fortyseven i)))))

(defun euler-fortysix ()
  (let* ((ts (loop for i from 1 upto 100 collect (* 2 i i) into res finally (return res)))
	(pr (loop for i from 1 upto 10000 when (fermat-primep i) collect i into res finally (return res)))
	 (sum-ts-pr (unique-elts (loop for i in ts append (loop for j in pr collect (+ i j) into res finally (return res)) into res finally (return res)))))
    (format t "Done With generation~%")
    (loop for i from 2 when (and (oddp i) (not (fermat-primep i)) (not (member i sum-ts-pr))) do (return-from euler-fortysix i))))

(defun euler-fortythree ()
  (loop for i in (mapcar #'(lambda (n) (concatenate 'string n)) (permutations '(#\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9 #\0)))
     when (and (= 0 (mod (parse-integer (subseq i 1 4)) 2))
	       (= 0 (mod (parse-integer (subseq i 2 5)) 3))
	       (= 0 (mod (parse-integer (subseq i 3 6)) 5))
	       (= 0 (mod (parse-integer (subseq i 4 7)) 7))
	       (= 0 (mod (parse-integer (subseq i 5 8)) 11))
	       (= 0 (mod (parse-integer (subseq i 6 9)) 13))
	       (= 0 (mod (parse-integer (subseq i 7 10)) 17)))
       collect (parse-integer i) into res finally (return (apply #'+ res))))

(defun euler-fortyfour ()
  (let ((pentn (loop for n from 1 upto 10000 collect (/ (- (* 3 n n) n) 2) into res finally (return res)))
	(min-dif 99999999))
    (loop for i from 0 upto (- (length pentn) 1) do
	 (progn (format t "Now at ~A and best is ~A~%" i min-dif)
		(loop for j from (+ 1 i) upto (- (length pentn) 1) when (let ((a (elt pentn i))
									      (b (elt pentn j))) 
									  (and (< (- b a) min-dif) 
									       (pentagonal-p (+ a b))
									       (pentagonal-p (- b a))))
		   do (setf min-dif (- (elt pentn j) (elt pentn i))))))
    min-dif))

(defun euler-fortynine ()
  (loop for i from 1000 upto 9999 when (let ((perms (permutations-number i))
					     (a (+ i 3330))
					     (b (+ i 6660)))  
					 (and (member a perms) (member b perms)
					      (every #'fermat-primep (list i a b))))
     collect (concatenate 'string (write-to-string i) (write-to-string (+ i 3330)) (write-to-string (+ i 6660))) into res
       finally (return res)))

(defun totient-naive (n)
  (loop for i from 1 upto (- n 1) counting (= 1 (gcd i n)) into tot finally (return tot)))

(defun totient (n)
  (loop for i in (unique-elts (prime-factorization n)) collecting (- 1 (/ 1 i)) into res finally (return (apply #'* (cons n res)))))

(defun euler-seventy ()
  (let ((min-ratio 99999999)
	(n-res 0)) 
    (loop for i from 2 upto 10000000
       do (let ((tot (totient i)))  
	    (when (and (< (/ i tot) min-ratio)
		       (member tot (permutations-number i)))
	      (setf min-ratio (/ i tot))
	      (setf n-res i)
	      (format t "Found new best at n=~A~%" i)))
	 finally (return n-res))))


(defun euler-sixtynine ()
  (loop with max-ratio = '0 and best-i for i from 2 upto 1000000 when (> (/ i (totient i)) max-ratio) 
     do (progn 
	  (setf best-i i)
	  (setf max-ratio (/ i (totient i)))
	  (format t "Found new best ratio ~A at i=~A~%" max-ratio best-i))
       finally (return best-i)))

(defun combinations (bag n)
  (when (or (= 0 n) (null bag)) 
    (return-from combinations (list nil)))
  (let ((cyclic-bag (copy-list bag))
	(len (length bag)))
    (setf (cdr (last cyclic-bag)) cyclic-bag)
    (when (= len n)
      (return-from combinations (permutations bag)))
    (loop for skip-count from 0 upto (- (- len n) 1) collect
	 (loop for sub-seq-count from 1 upto (/ (lcm len n) n)
	    collect (cons (elt cyclic-bag (1- sub-seq-count)) 
			  (subseq cyclic-bag (+ skip-count sub-seq-count) (1- (+ n skip-count sub-seq-count))))))))

(defun euler-ninetythree ()
  (let* ((ops (list #'+ #'- #'* #'/))
	 (digits (permutations (list 1 2 3 4 5 6 7 8 9))))
    (setf ops (mapcar #'cdr (permutations ops)))
    (mapc #'(lambda (x) (setf (cddddr x) nil)) (permutations digits))
    (list ops digits)))
