import fuzzysat
import fuzzysat.z3 as z3

s = fuzzysat.FuzzySolver(b"\x00\x00\x00\x00")

c = z3.Concat(
    z3.BitVec(0, 8),
    z3.BitVec(1, 8),
    z3.BitVec(2, 8),
    z3.BitVec(3, 8)) == 42
s.ctx.print_expr(c)

print(s.check_sat(c))
