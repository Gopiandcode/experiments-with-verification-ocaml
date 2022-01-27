# Experiments with verifying OCaml code

This project consists of a series of experiments of verifying OCaml code in Coq.


Once you have installed the requirements, build the programs and their proofs with dune:
```
opam exec -- dune build @all
```

## Requirements

- Coq-cfml >= 20220112
- OCaml

Once you have the coq-repositories added:

```
opam repo add coq-released https://coq.inria.fr/opam/released
```

Simply install cfml:
```
opam install cfml coq-cfml
```

## Project Structure

```
.
├── lib                OCaml code
├── proofs             Coq proofs 
├── src                Entry point
├── dune-project
└── Readme.md


4 directories, 2 files
```

