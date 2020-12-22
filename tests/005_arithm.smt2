(declare-const k!0 (_ BitVec 8))
(declare-const k!1 (_ BitVec 8))
(declare-const k!2 (_ BitVec 8))
(declare-const k!3 (_ BitVec 8))

(assert
	(and
		(bvult
			#x0000ffff
			(bvadd 
				(concat k!0 k!1 k!2 k!3)
				#xabadcafe))
		(bvugt
			#x00010001
			(bvadd 
				(concat k!0 k!1 k!2 k!3)
				#xabadcafe))))
