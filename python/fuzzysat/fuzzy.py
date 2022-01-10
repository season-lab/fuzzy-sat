import tempfile
import ctypes
import os

from .z3 import main_ctx as _z3_ctx
from .z3 import BitVec, BitVecRef, BoolVal, And

SCRIPTDIR = os.path.realpath(os.path.dirname(__file__))

libref = ctypes.cdll.LoadLibrary(
    os.path.join(SCRIPTDIR, "libfuzzy_python.so"))
libref.z3fuzz_create.restype = ctypes.c_void_p

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
    def __init__(self, seed:bytes, timeout:int=0):
        self._tmpfile = tempfile.NamedTemporaryFile()
        self._tmpfile.write(seed)
        self._tmpfile.flush()

        self.ctx = FuzzyCtx(self._tmpfile.name, timeout)
        self.constraints = list()
        self.inputs = [BitVec(i, 8) for i in range(len(seed))]

    def __del__(self):
        self._tmpfile.close()

    def get_input(self, off):
        if off >= len(self.inputs) or off < 0:
            raise ValueError("off is not a valid input")
        return self.inputs[off]

    def add(self, constraint:BitVecRef):
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
            return False, None
        return True, (ctypes.c_char*proof_size.value).from_address(proof.value).raw

    def eval_upto(self, expr:BitVecRef, n:int, use_gd=False, gd_to_max=True):
        out_arr = (ctypes.c_uint64 * n)(*([0]*n))

        gd_mode = 0
        if use_gd and not gd_to_max:
            gd_mode = 1
        elif use_gd and gd_to_max:
            gd_mode = 2

        n_vals = libref.evalUpto(
            self.ctx.handle_ref(),
            expr.as_ast(),
            self.pi().as_ast(),
            ctypes.byref(out_arr),
            ctypes.c_uint32(n),
            ctypes.c_uint8(gd_mode))

        return list({out_arr[i] for i in range(n_vals)})
