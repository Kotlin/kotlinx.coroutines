Formal proofs
=============

Overview
--------

This directory contains formally verified proofs of the data structures
implemented in the code.

Building
--------

First, it is required to install [Coq](https://coq.inria.fr/) along with the
[Iris Framework](https://iris-project.org/). For detailed instuctions on that,
see the description in the repository of Iris
[here](https://gitlab.mpi-sws.org/iris/iris/blob/master/README.md).

This project was successfully built with version `dev.2019-07-01.1.6e79f000` of
Iris.

After Iris is installed and the toolchain of Coq is in `$PATH`, run
```sh
coq_makefile -f _CoqProject -o Makefile.coq.local
make -f Makefile.coq.local
```

Structure
---------

### Overview

* `_CoqProject` is the description of the project for the build systems of Coq.
* `theories` is the directory with the source code.

### Theories

* `algebra` contains resource algebras (see the
  [formal documentation on Iris](https://plv.mpi-sws.org/iris/appendix-3.1.pdf))
  needed to express ownership of logical parts of the described data structures.
* `lib` contains proofs of the structures. Files `$x_impl` contain the concrete
  code that was verified; `$x_spec` describe the desired behavior of that code;
  `$x_proof` ensure that the code meets these expectations.
* `util` contains various useful lemmas and contructs about objects that are
  universal and not directly relevant to the subject matter. In an ideal world,
  these constructs would be in one standard library or the other.
