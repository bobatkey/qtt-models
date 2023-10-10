# Supplementary material for "Polynomial Time and Dependent Types"

## To build

1. Easiest (if you have `nix`):

   ```
   nix build .#supplementary-material
   ```

   ought to check the Agda code and generate the HTML documentation in
   a `result` folder.

2. Otherwise:

   Install Agda 2.6.2.2 and the standard library 1.7.1.

   Load the file `src/Everything.agda` with Emacs and check with `C-c
   C-l`. The comments in `Everything` document the parts of the paper
   each section corresponds to.

## For the generated material:

The Agda source files referred to in Sections 5 and 6 of the
submission are in the directory `src/`.

They have been checked with Agda 2.6.2.2 and standard library version
1.7.1.

The module `Everything.agda` imports the main modules referred to in
the submission.

The HTML generated from the source files is in `html/`. Again, please
refer to the `Everything.html` module for entry points.
