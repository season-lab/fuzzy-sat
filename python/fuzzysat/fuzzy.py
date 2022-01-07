import tempfile
import ctypes
import os

from .z3 import main_ctx as _z3_ctx
from .z3 import BitVecRef, BoolVal, And

SCRIPTDIR = os.path.realpath(os.path.dirname(__file__))

libref = ctypes.cdll.LoadLibrary(
    os.path.join(SCRIPTDIR, "libZ3Fuzzy.so"))
libref.z3fuzz_create.restype = ctypes.c_void_p

class FuzzyCtx(object):
    def __init__(self, seed:str, timeout:int=0):
        native_z3_ctx  = ctypes.c_void_p(_z3_ctx().ctx.value)
        native_seed    = ctypes.c_char_p(bytes(seed, "ascii"))
        native_timeout = ctypes.c_void_p(timeout)

        self.handle = libref.z3fuzz_create(native_z3_ctx, native_seed, native_timeout)

    def print_expr(self, expr:BitVecRef):
        libref.z3fuzz_print_expr(self.handle_ref(), expr.as_ast())

    def handle_ref(self):
        return ctypes.c_void_p(self.handle)

    def __del__(self):
        libref.z3fuzz_free(self.handle_ref())

class FuzzySolver(object):
    def __init__(self, seed:bytes, timeout:int=0):
        self._tmpfile = tempfile.NamedTemporaryFile()
        self._tmpfile.write(seed)
        self._tmpfile.flush()

        self.ctx = FuzzyCtx(self._tmpfile.name, timeout)
        self.constraints = list()

    def __del__(self):
        self._tmpfile.close()

    def notify_constraint(self, constraint:BitVecRef):
        self.constraints.append(constraint)

        libref.z3fuzz_notify_constraint(
            self.ctx.handle_ref(), constraint.as_ast())

    def check_sat(self, branch_condition:BitVecRef):
        proof_size = ctypes.c_uint64()
        proof      = ctypes.c_uint64()

        query = BoolVal(True)
        if self.constraints:
            query = And(*self.constraints)

        res = libref.z3fuzz_query_check_light(
            self.ctx.handle_ref(),
            query.as_ast(),
            branch_condition.as_ast(),
            ctypes.byref(proof),
            ctypes.byref(proof_size))

        if res == 0:
            return False, None
        return True, (ctypes.c_char*proof_size.value).from_address(proof.value).raw
