import os
from subprocess import check_call
from shutil import copyfile

CURRENT_DIR = os.path.dirname(os.path.realpath(__file__))


def run_experiment(path_to_queries, path_to_seed):
    # fuzzy_solver

    exp_dir = CURRENT_DIR + "/data/" + \
        path_to_queries.split("/")[-1].replace(".smt2.tar.gz", "")
    try:
        # Create experiment directory
        os.mkdir(exp_dir)
    except FileExistsError:
        print("Dicrectory ", exp_dir,  " already exists")
        return -1

    stdout_file_fuzzy_solver = open(exp_dir + "/stdout_fuzzy.txt", "w")
    stderr_file_fuzzy_solver = open(exp_dir + "/stderr_fuzzy.txt", "w")

    print("running fuzzy-solver on", path_to_queries)
    check_call([CURRENT_DIR + "/decompress_and_run.sh", CURRENT_DIR + "/../fuzzy-solver",
                path_to_queries, path_to_seed], stderr=stderr_file_fuzzy_solver)

    copyfile("/tmp/z3fuzzy-log.csv", exp_dir + "/fuzzy-solver.csv")
    copyfile("/tmp/sat-z3-only.smt2", exp_dir + "/sat-z3-only.smt2")
    stderr_file_fuzzy_solver.close()
    stdout_file_fuzzy_solver.close()

    stdout_file_solver = open(exp_dir + "/stdout_solver.txt", "w")
    stderr_file_solver = open(exp_dir + "/stderr_solver.txt", "w")

    print("running solver on", path_to_queries)
    check_call([CURRENT_DIR + "/decompress_and_run.sh", CURRENT_DIR + "/../solver",
                path_to_queries], stderr=stderr_file_solver)

    copyfile("/tmp/z3fuzzy-log.csv", exp_dir + "/solver.csv")
    stderr_file_solver.close()
    stdout_file_solver.close()

    return 0


run_experiment("/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/lodepng_queries.smt2.tar.gz",
               "/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/png.seed")

run_experiment("/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/lodepng_nocks_queries.smt2.tar.gz",
               "/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/png.seed")

run_experiment("/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/libpng_queries.smt2.tar.gz",
               "/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/png.seed")

run_experiment("/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/djpeg_queries.smt2.tar.gz",
               "/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/jpg.seed")

run_experiment("/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/gifhisto_queries.smt2.tar.gz",
               "/mnt/data/symbolic/SymFuzz/fuzzy-solver/query_db/gif.seed")
