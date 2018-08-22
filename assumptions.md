This project's ASN.1 Real encoding implementation  is designed to comply with the definitions set out by [ISO/IEC 8825-1:2015 Standard](https://www.iso.org/standard/68345.html), in particular, with the Basic Encoding Rules, described in section [8].

However, the following limitations currently apply:

* Only binary encoding [8.5.7] is considered, leaving decimal encoding [8.5.8] out of the project`s scope.
* Only short form [8.1.3.4] encoding is considered, leaving long form [8.1.3.5] out of the project's scope.
* No debugging payload can be carried by ASN.1 Real `NOT-A-NUMBER` value [8.5.9]. Thus, when converting from IEEE-754 to ASN.1, any additional information is lost. When converting from ASN.1 to IEEE-754 debugging payload is set to `0`.
* No rounding  or arithmetic rules are imposed on ASN.1 reals, as those are not specified by the standard.
