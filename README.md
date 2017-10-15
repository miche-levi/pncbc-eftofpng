# EFTofPNG

This is a Mathematica package for high precision computation with the Effective
Field Theory of Post-Newtonian Gravity. Its aim is to provide computer-algebra
tools that can be used to derive analytical input for gravitational-wave source
modelling relevant to current observatories. An example application provided
with the code is the derivation of all currently known spin-dependent
conservative interaction potentials in the post-Newtonian (PN) approximation to
General Relativity (GR).

For a nontechnical description of the package and supplementary documentation
see [arxiv.org:1705.06309](https://arxiv.org/abs/1705.06309).


## Getting started

### Prerequisites

You need [Mathematica](https://www.wolfram.com/mathematica/) and the
[xTensor package](http://xact.es/xTensor/). For the latter, follow its
[installation instructions](http://xact.es/download/install). Then, of course,
clone this repository:

```
git clone https://github.com/miche-levi/pncbc-eftofpng.git
```

### Using the package

The package is modularized into several .m files. In order to run the standard
examples, successively open the files with the Mathematica interface and click
"Run Package" on the top-right corner, in the following order:

1. FeynRul.m - compute Feynman rules
2. FeynGen.m - generate Feynman diagrams
3. NLoop.m - compute master integrals
4. EFTofPNG.m - calculate the post-Newtonian Lagrangian

A good starting point to explore the code is the example calculation of the
2PN point-mass Lagrangian in the section FeynComp of EFTofPNG.m. The Feynman
diagrams are stored in a variable ```L2PNdiagrams```, you can visualize them
with ```MakePNGraphs[L2PNdiagrams]```.

### How can I do ...?

The code is designed in a manner that is very extensible to new applications.
Yet this requires experience with Mathematica. The code is not a black box 
that can write a paper for you. We invite you to join in and participate in 
extending the code for further nontrivial applications that you have in mind. 

### Just interested in the current results?

You can find the (conservative) post-Newtonian GR Lagrangian including all
currently known spin-dependent potentials in
[results/LEFT.dat.m](results/LEFT.dat.m).


## Contributing

Please read the file [CodingStyle.m](CodingStyle.m). Feedback and feature
requests are also very much appreciated.


## Authors

* **Michele Levi** - [miche-levi](https://github.com/miche-levi/)
* **Jan Steinhoff** - [jsteinhoff](https://github.com/jsteinhoff/)


## License

This project is licensed under the GPL version 3, see the [COPYING](COPYING)
file.


## Acknowledgments

It would have been much more difficult to create such a flexible package without
building on the [xTensor package](http://xact.es/xTensor/). Let's all share our
codes, so everyone can focus more on science!
