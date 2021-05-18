# Stabilizer Hamiltonian Degeneracy
Calculate the ground state degeneracy (GSD) of a Z<sub>N</sub> stabilizer Hamiltonian H, \
which consists of a sum of products of Z<sub>N</sub> Pauli operators (with negative coefficients), \
so that each operator has eigenvalue +1 in the ground states.

[degen.nb][] is a user friendly Mathematica script to perform the GSD calculation, even for nonprime N. \
To download, right click the link below and select "Save link as...": \
<https://github.com/kjslag/degeneracy/raw/master/degen.nb>

[degen.hs][] is an undocumented but faster haskell script to calculate the GSD.

The GSD is calculated using the algorithm described in Appendix B of [1], which is based on [2,3]. \
[1] Shirley, Slagle, Chen, "Twisted foliated fracton phases", PRB (2020), https://arxiv.org/abs/1907.09048 \
[2] Gheorghiu, "Standard form of qudit stabilizer groups", PRA (2014), https://arxiv.org/abs/1101.1519 \
[3] Gottesman, "Stabilizer codes and quantum error correction", PhD Thesis (1997), https://arxiv.org/abs/quant-ph/9705052

[degen.nb]: degen.nb
[degen.hs]: degen.hs
