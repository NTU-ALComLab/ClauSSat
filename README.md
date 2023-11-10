# ClauSSat
This repository is an implementation of the 2021 AAAI paper titled "A Sharp Leap from Quantified Boolean Formulas to Stochastic Boolean Satisfiability Solving". The implementation of strategy generation is proposed in "SharpSSAT: A Witness-Generating Stochastic Boolean Satisfiability Solver".
To compile, type
```
$ make
```
The default options for ClauSSat is set as `-sguwc`. Use the `-h` flag for more information about supported options.

For strategy generation capability, set the option as `-sguwck`. It will generate a multi-output Boolean function in the same path as the input instance, each output represent the strategy of the corresponding existential variables. The strategy file is in the BLIF format.

Below are the options used for different versions of the clause selection framework. 
```
original version: [-ge]
cued version: [-geuw]
cued+UAS vesion: [-geuwn]
certificate: +[-k]
qesto certificate: [-genk]
cued certificate: [-geuwnk]
onset/careset: +[-km] //must with certificate option
```
