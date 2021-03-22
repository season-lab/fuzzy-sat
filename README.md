# Fuzzy SAT

[![CircleCI](https://circleci.com/gh/season-lab/fuzzy-sat.svg?style=shield&circle-token=426e6fc0f049c0a748ff3487716cb303ebe9a918)](https://app.circleci.com/pipelines/github/season-lab/fuzzy-sat)

### Build

Clone the repository and all the submodules:
``` bash
$ git clone https://github.com/season-lab/fuzzy-sat 
$ cd fuzzy-sat
$ git submodule update --init --recursive
```

Build the library using `cmake`:
``` bash
$ cd path/to/build/dir
$ cmake -DCMAKE_BUILD_TYPE=Release path/to/fuzzy-sat/source
$ make
```

It will build our fork of z3, the FuzzySAT library, and the command-line tools.

### How to use
See https://season-lab.github.io/fuzzolic/usage.html#fuzzy-sat.

### Query Dataset

- queries: https://drive.google.com/file/d/1aTBMcWr6pzPNkVyJQnHqpxi2_xz8qgeu/view?usp=sharing
- queries_single: https://drive.google.com/file/d/1MirAWRtEZmDubAsQrAUW62Woi5hnCwCy/view?usp=sharing
- seeds:   https://drive.google.com/file/d/1x9da_dbbaI6DOPScbWzfl5K_WzStLy3L/view?usp=sharing

**NOTE**: The queries in *queries_single* and *queries* are exactly the same. But in *queries_single*, each query is splitted in a single file.
