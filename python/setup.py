import multiprocessing
import subprocess
import shutil
import os

from setuptools import setup, find_packages
from distutils.command.build import build as _build
from distutils.command.clean import clean as _clean

SCRIPTDIR = os.path.realpath(os.path.dirname(__file__))

def _patch_z3():
    os.system(
        "sed -i '13 {s/^/#/}' %s" % "fuzzysat/z3/z3core.py"
    )
    os.system(
        "sed -i '8 {s/^/import sys, io; import fuzzysat.z3 as z3 #/}' %s" % "fuzzysat/z3/z3printer.py"
    )

def _build_native():
    build_dir = os.path.realpath(os.path.join(SCRIPTDIR, "../build-cmake"))
    if not os.path.exists(build_dir):
        os.mkdir(build_dir)

    cmd = ["cmake", "-DCMAKE_BUILD_TYPE=Debug", ".."]
    subprocess.check_call(cmd, cwd=build_dir)

    cmd = ["make", "-j", str(multiprocessing.cpu_count())]
    subprocess.check_call(cmd, cwd=build_dir)

    shutil.rmtree('fuzzysat/z3', ignore_errors=True)
    shutil.rmtree('fuzzysat/libZ3Fuzzy.so', ignore_errors=True)

    shutil.copytree(
        os.path.join(build_dir, "fuzzolic-z3", "python", "z3"),
        "fuzzysat/z3"
    )
    shutil.copy(
        os.path.join(build_dir, "fuzzolic-z3", "python", "libz3.so"),
        "fuzzysat/z3/libz3.so"
    )
    shutil.copy(
        os.path.join(build_dir, "lib", "libZ3Fuzzy.so"),
        "fuzzysat/libZ3Fuzzy.so"
    )

    _patch_z3()

def _clean_native():
    pass

class build(_build):
    def run(self, *args):
        self.execute(_build_native, (), msg='Building fuzzysat')
        _build.run(self, *args)

class clean(_clean):
    def run(self, *args):
        self.execute(_clean_native, (), msg='Cleaning fuzzysat')
        _clean.run(self, *args)

cmdclass = {
    'build': build,
    'clean': clean,
}

setup (
    name='fuzzysat',
    version='0.1',
    python_requires='>=3.6',
    description='An approximate SMT solver',
    url='https://github.com/season-lab/fuzzy-sat',
    packages=find_packages(),
    install_requires=[],
    setup_requires=[],
    extras_require={},
    cmdclass=cmdclass,
    include_package_data=True,
    package_data={
        'fuzzysat': [
            'z3/*',
            'libZ3Fuzzy.so',
        ]
    }
)
