xquery version "3.1";
import module namespace gr = "http://snelson.org.uk/functions/grammar" at "/db/apps/parser/grammar.xq";
import module namespace p = "http://snelson.org.uk/functions/parser" at "/db/apps/parser/parser.xq";

let $rules :=
(
  gr:rule-("M",gr:choice("V","Apply","Define","String")),
  gr:rule("Apply",("LP","M","M","RP")),
  gr:rule("Define",("LP",gr:term-("lambda"),"V","Dot","M","RP")),
  gr:rule("V",gr:choice(gr:char-range("a","z"),gr:char-range("A","Z"))),
  gr:rule("String",(gr:term-('"'),gr:zero-or-more(gr:choice(gr:codepoint-range(9,33),gr:codepoint-range(35,127))),gr:term-('"')),"ws-explicit"),
  gr:token-("LP",gr:term("(")),
  gr:token-("RP",gr:term(")")),
  gr:token-("Dot",gr:term(".")),
  gr:ws("S",gr:choice(gr:term(" "),gr:term("&#9;"),gr:term("&#10;"),gr:term("&#13;"))),
  gr:ws("Comment",(gr:term("/*"),gr:zero-or-more(gr:term("*")),gr:term("*/")))
)
let $rs :=
 for $r in $rules
 return
     $r($p:generate-default-actions)
return
    $rs