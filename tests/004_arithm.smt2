(declare-const k!0 (_ BitVec 8))
(declare-const k!1 (_ BitVec 8))
(declare-const k!2 (_ BitVec 8))
(declare-const k!3 (_ BitVec 8))

(assert
	(and
		(bvult
			#x0000ffff
			(concat k!0 k!1 k!2 k!3))
		(bvugt
			#x00010001
			(concat k!0 k!1 k!2 k!3))))
