This project's ASN.1 Real encoding implementation  is designed to comply with the definitions set out by [ISO/IEC 8825-1:2015 Standard](https://www.iso.org/standard/68345.html), in particular, with the Basic Encoding Rules, described in section [8].

However, the following limitations currently apply:

* Only binary encoding [8.5.7] is considered, leaving decimal encoding [8.5.8] out of the project's scope.
* Only short form [8.1.3.4] encoding is considered, leaving long form [8.1.3.5] out of the project's scope.
* No rounding  or arithmetic rules are imposed on ASN.1 reals, as those are not specified by the standard.
* Conversion between formats corresponding to IEEE-754 and ASN.1 have the following restrictions:
	* IEEE -> ASN
		* Only direct conversion is attempted (i.e. the representation s\*m\*2^e is only converted into the same format without tweaking any variables (s,m,e) or the radix.
		* No debugging payload can be carried by ASN.1 Real `NOT-A-NUMBER` value [8.5.9]. Thus, when converting from IEEE-754 to ASN.1, any additional information is lost.
		* Converted IEEE-754 format needs to be "meaningful" (i.e. have a positive number of explicit significand bits).
	* ASN -> IEEE
		* The resulting IEEE-754 format (e.g. Binary32, Binary64, ...) needs to be explicitly specified for every conversion.
		* The resulting IEEE-754 format needs to be "meaningful" (i.e. have a positive number of explicit significand bits).
		* Only ASN.1 values having `radix = 2` are converted, switching radices is not currently supported. Thus trying to convert an ASN.1 real number with base 4, 8 or 16 to IEEE-754 format will yield `None`.
		* Only direct conversion is attempted (i.e. the representation s\*m\*2^e is only converted into the same format without tweaking any variables (s,m,e) or the radix.
		* No debugging payload can be carried by ASN.1 Real `NOT-A-NUMBER` value [8.5.9]. Thus, when converting from ASN.1 to IEEE-754, debugging payload is set to `0`.
