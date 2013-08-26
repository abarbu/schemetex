(module schemetex-blahtex *
(import chicken scheme foreign)

#>
char *texToMathML(char *inputUtf8);
<#

(define blahtex (foreign-lambda c-string* "texToMathML" c-string))
)
