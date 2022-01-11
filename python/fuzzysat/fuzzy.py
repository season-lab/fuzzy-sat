import tempfile
import ctypes
import os

from .z3 import main_ctx as _z3_ctx
from .z3 import BitVec, BitVecRef, BoolVal, BoolRef, And

class evalElement(ctypes.Structure):
    _fields_ = [('val', ctypes.c_uint64),
                ('proof', ctypes.c_uint64),
                ('proof_size', ctypes.c_uint64)]

SCRIPTDIR = os.path.realpath(os.path.dirname(__file__))

libref = ctypes.cdll.LoadLibrary(
    os.path.join(SCRIPTDIR, "libfuzzy_python.so"))

libref.createFuzzyCtx.restype             = ctypes.c_void_p
libref.createEvalElementArray.restype     = ctypes.POINTER(evalElement)
libref.z3fuzz_evaluate_expression.restype = ctypes.c_uint64
libref.z3fuzz_maximize.restype            = ctypes.c_uint64
libref.z3fuzz_minimize.restype            = ctypes.c_uint64

class FuzzyCtx(object):
    def __init__(self, seed:str, timeout:int=0):
        native_z3_ctx  = ctypes.c_void_p(_z3_ctx().ctx.value)
        native_seed    = ctypes.c_char_p(bytes(seed, "ascii"))
        native_timeout = ctypes.c_void_p(timeout)

        self.handle = libref.createFuzzyCtx(native_z3_ctx, native_seed, native_timeout)

    def print_expr(self, expr:BitVecRef):
        libref.z3fuzz_print_expr(self.handle_ref(), expr.as_ast())

    def handle_ref(self):
        return ctypes.c_void_p(self.handle)

    def __del__(self):
        libref.destroyFuzzyCtx(self.handle_ref())

class FuzzySolver(object):
    def __init__(self, seed:bytes, timeout:int=1000):
        with tempfile.NamedTemporaryFile() as f:
            f.write(seed)
            f.flush()
            self.ctx = FuzzyCtx(f.name, timeout)

        self.seed = seed
        self.constraints = list()
        self.inputs = [BitVec(i, 8) for i in range(len(seed))]

    def __del__(self):
        pass

    def get_input(self, off:int):
        if off >= len(self.inputs) or off < 0:
            raise ValueError(f"{off} is not a valid offset")
        return self.inputs[off]

    def add(self, constraint:BoolRef):
        if not self.eval_in_seed(constraint) > 0:
            raise ValueError(
                "the constraint is not true when evaluated in the seed")
        self.constraints.append(constraint)

        libref.z3fuzz_notify_constraint(
            self.ctx.handle_ref(), constraint.as_ast())

    def pi(self):
        pi = BoolVal(True)
        if self.constraints:
            pi = And(*self.constraints)
        return pi

    def check_sat(self, branch_condition:BitVecRef):
        proof_size = ctypes.c_uint64()
        proof      = ctypes.c_uint64()

        res = libref.z3fuzz_query_check_light(
            self.ctx.handle_ref(),
            self.pi().as_ast(),
            branch_condition.as_ast(),
            ctypes.byref(proof),
            ctypes.byref(proof_size))

        if res == 0:
            optsol = libref.z3fuzz_get_optimistic_sol(
                self.ctx.handle_ref(),
                ctypes.byref(proof),
                ctypes.byref(proof_size))
            if optsol == 0:
                return False, False, None
            return False, True, (ctypes.c_char*proof_size.value).from_address(proof.value).raw
        return True, True, (ctypes.c_char*proof_size.value).from_address(proof.value).raw

    def eval_in_seed(self, expr:BitVecRef):
        seed_arr = (ctypes.c_uint8 * len(self.seed))(*list(self.seed))
        return libref.z3fuzz_evaluate_expression(
            self.ctx.handle_ref(),
            expr.as_ast(),
            seed_arr
        )

    def eval_upto_inner(self, expr:BitVecRef, n:int, mode="greedy"):
        if mode not in {"greedy", "gd_min", "gd_max"}:
            raise ValueError("unrecognised mode")

        out_arr = libref.createEvalElementArray(
            ctypes.c_uint64(n),
            ctypes.c_uint64(len(self.seed))
        )

        if mode == "greedy":
            gd_mode = 0
        elif mode == "gd_min":
            gd_mode = 1
        else:
            gd_mode = 2

        n_vals = libref.evalUpto(
            self.ctx.handle_ref(),
            expr.as_ast(),
            self.pi().as_ast(),
            out_arr,
            ctypes.c_uint32(n),
            ctypes.c_uint8(gd_mode))

        inserted_vals = set()
        res = list()
        for i in range(n_vals):
            if out_arr[i].val in inserted_vals:
                continue

            inserted_vals.add(out_arr[i].val)
            res.append(
                (out_arr[i].val, (ctypes.c_char*out_arr[i].proof_size).from_address(out_arr[i].proof).raw)
            )

        libref.destroyEvalElementArray(
            out_arr,
            ctypes.c_uint64(n))
        return res

    def eval_upto(self, expr:BitVecRef, n:int):
        added_elements = set()
        res = list()

        for el in \
                self.eval_upto_inner(expr, n, "greedy") + \
                self.eval_upto_inner(expr, n, "gd_min") + \
                self.eval_upto_inner(expr, n, "gd_max"):

            if el[0] in added_elements:
                continue
            added_elements.add(el[0])
            res.append(el)
        return res[:n]

    def minimize(self, expr:BitVecRef):
        proof_size = ctypes.c_uint64()
        proof      = ctypes.c_uint64()

        minval = libref.z3fuzz_minimize(
            self.ctx.handle_ref(),
            self.pi().as_ast(),
            expr.as_ast(),
            ctypes.byref(proof),
            ctypes.byref(proof_size))

        return minval, (ctypes.c_char*proof_size.value).from_address(proof.value).raw

    def maximize(self, expr:BitVecRef):
        proof_size = ctypes.c_uint64()
        proof      = ctypes.c_uint64()

        maxval = libref.z3fuzz_maximize(
            self.ctx.handle_ref(),
            self.pi().as_ast(),
            expr.as_ast(),
            ctypes.byref(proof),
            ctypes.byref(proof_size))

        return maxval, (ctypes.c_char*proof_size.value).from_address(proof.value).raw
