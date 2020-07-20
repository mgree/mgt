What is this repository for?

This is the AEC repository for the POPL 2018 paper titled "Migrating Gradual Types"
How do I get set up?

To perform the evaluation, you need a recent GHC. I used GHC 8.0.2 on Ubuntu 16.04. However, the project uses only standard packages so should work with older versions (if not too old), too.

To start evaluate the artifact, first clone the repository. After that, go to the directory, and type ghci Eval.hs, which should direct you to the interactive version of GHC. The main entry for evaluation is measureRand, which takes too arguments. The first argument denotes the size of the program (in LOC), such as 10000, 20000, 30000, etc. The second argument represents how many programs of the specified size need to be generated. For example, this is one instance of calling it.

*Eval> measureRand 20000 3

....lots of junk

Summary of evaluation....

Gradual time duration: 6.112049390666667s

Migrational time duration: 9.877710201333334s

# of Best migration: 800

Average LOC: 19992

Average # of funcs: 5562

Average # of dynamic args: 9917

These values roughly correspond to the columns in Figure 10 in the POPL paper. Here I used "roughly" because the program generation process is randomized using the Haskell function randomRIO, which implies that each time the program is run, the generated program will be different. Nevertheless, all the results should be close to the values in Figure 10. Most importantly, the claim "The results show that migrational typing scales linearly with the size of the program and takes only 2–4 times longer than plain gradual typing." (from the abstract and Section 9) holds for any program size. 