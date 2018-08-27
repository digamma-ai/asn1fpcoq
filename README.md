# asn1fpcoq
ASN.1 Floating Point encoding formalized in Coq
## Features
* High-level ASN.1 Real definition
* TODO: Bit-string encoding of ASN.1 real numbers
* TODO: Conversion between ASN.1 and Flocq IEEE-745
## Prerequisites
* [Coq](https://coq.inria.fr/)  
`opam repo add coq-released http://coq.inria.fr/opam/released`  
`opam install coq`  
* [Flocq](http://flocq.gforge.inria.fr/)  
`opam install coq-flocq`
## Acknowledgements
* Thanks to [Sylvie Boldo](https://www.lri.fr/~sboldo/) and [Guillaume Melquiond](https://www.lri.fr/~melquion/) for their development of the [Floats for Coq](http://flocq.gforge.inria.fr/) library, on which this project heavily relies both abstractly and with code.
* Thanks to [Yury Strozhevsky](https://www.strozhevsky.com/) for the great articles explaining  the basics of ASN.1 encoding.
