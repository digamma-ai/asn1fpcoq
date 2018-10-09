# asn1fpcoq
ASN.1 Floating Point encoding formalized in Coq

## Features
* High-level ASN.1 Real definition 
* Conversion between ASN.1 and Flocq IEEE-754
* TODO: Bit-string encoding of ASN.1 real numbers
## Assumptions
See [doc/assumptions.md](https://github.com/digamma-ai/asn1fpcoq/blob/master/assumptions.md)

## Prerequisites
* [Coq 8.7.2](https://coq.inria.fr/)  
* [Flocq](http://flocq.gforge.inria.fr/)  
* [ExtLib](https://github.com/coq-ext-lib/coq-ext-lib)
* [Dune](https://github.com/ocaml/dune)  

To install all pre-requisites:

    opam repo add coq-released http://coq.inria.fr/opam/released
    opam pin add coq 8.7.2
    opam install coq coq-ext-lib coq-flocq dune

## Acknowledgements
* Thanks to [Sylvie Boldo](https://www.lri.fr/~sboldo/) and [Guillaume Melquiond](https://www.lri.fr/~melquion/) for their development of the [Floats for Coq](http://flocq.gforge.inria.fr/) library, on which this project heavily relies both abstractly and with code.
* Thanks to [Yury Strozhevsky](https://www.strozhevsky.com/) for the great articles explaining  the basics of ASN.1 encoding.
* Thanks to all the authors and contributors of the [StructTact](https://github.com/uwplse/StructTact) library.
