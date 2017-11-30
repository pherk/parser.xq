xquery version "3.1";

(:
 : Copyright (c) 2013 John Snelson
 :
 : Licensed under the Apache License, Version 2.0 (the "License");
 : you may not use this file except in compliance with the License.
 : You may obtain a copy of the License at
 :
 :     http://www.apache.org/licenses/LICENSE-2.0
 :
 : Unless required by applicable law or agreed to in writing, software
 : distributed under the License is distributed on an "AS IS" BASIS,
 : WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 : See the License for the specific language governing permissions and
 : limitations under the License.
 :)

module namespace p = "http://snelson.org.uk/functions/parser";
declare default function namespace "http://snelson.org.uk/functions/parser";
declare namespace err = "http://www.w3.org/2005/xqt-errors";
import module namespace hmap = "http://snelson.org.uk/functions/hashmap" at "lib/hashmap.xq";
import module namespace sarray = "http://snelson.org.uk/functions/array" at "lib/array.xq";
import module namespace hamt = "http://snelson.org.uk/functions/hamt" at "lib/hamt.xq";
import module namespace gr = "http://snelson.org.uk/functions/grammar" at "grammar.xq";
import module namespace pr = "http://snelson.org.uk/functions/parser-runtime" at "lib/parser-runtime.xq";

declare variable $p:isMarkLogic as xs:boolean external :=
  fn:exists(fn:function-lookup(fn:QName("http://marklogic.com/xdmp","functions"),0));

declare variable $p:log := (
  fn:function-lookup(fn:QName("http://marklogic.com/xdmp","log"),1),
  function($s) { () }
)[1];

declare variable $p:eval := (
  fn:function-lookup(fn:QName("http://marklogic.com/xdmp","eval"),1),
  function($s) { fn:error(xs:QName("p:EVAL"),"Eval function unknown for this XQuery processor") }
)[1];

(: -------------------------------------------------------------------------- :)
(: Built-In Actions :)

declare variable $p:parse-default-actions := (
  p:discard#1,
  (: fn:codepoints-to-string#1, :)
  p:children#1,
  p:children#1,
  p:children#1,
  function($n) { p:tree($n,?) },
  function($n) { p:attr($n,?) }
);

declare variable $p:generate-default-actions := (
  "()",
  "$ch",
  "$ch",
  "$ch",
  function($n) {
    if(try { fn:empty(xs:NCName($n)) } catch * { fn:true() }) then
      fn:error(xs:QName("p:BADNAME"),"Invalid rule name: " || $n)
    else "function() {
      element " || $n || " { $ch ! (
        typeswitch(.)
        case xs:string return text { . }
        case xs:integer return text { fn:codepoints-to-string(.) }
        default return .()
      )}
    }"
  },
  function($n) {
    if(try { fn:empty(xs:NCName($n)) } catch * { fn:true() }) then
      fn:error(xs:QName("p:BADNAME"),"Invalid rule name: " || $n)
    else "function() {
      attribute " || $n || " { fn:string-join($ch ! (
        typeswitch(.)
        case xs:string return .
        case xs:integer return fn:codepoints-to-string(.)
        default return .() ! fn:string(.)
      ))}
    }"
  }
);


declare function p:tree($n,$ch)
{
  function() {
    element { $n } {
      $ch ! (
        typeswitch(.)
        case xs:string return text { . }
        case xs:integer return text { fn:codepoints-to-string(.) }
        default return .()
      )
    }
  }
};
 
declare function p:attr($n,$ch)
{
  function() {
    attribute { $n } { fn:string-join(
      $ch ! (
        typeswitch(.)
        case xs:string return text { . }
        case xs:integer return text { fn:codepoints-to-string(.) }
(:  AST error
 :        default return .() ! fn:string(.)
 :)
        default return .()
      )
    )}
  }
};

declare function p:children($ch)
{
  $ch
};

declare function p:discard($ch)
{
  ()
};

declare %private function p:codepoint($c)
{
  switch($c)
  case 0 return "\0"
  case 9 return "\t"
  case 10 return "\n"
  case 13 return "\r"
  case 34 return '\"'
  case 92 return "\\"
  default return fn:codepoints-to-string($c)
};

declare %private function p:codepoint-xq($c)
{
  switch($c)
  case 0 return "\0"
  case 9 return "\t"
  case 10 return "\n"
  case 13 return "\r"
  case 34 return "\&amp;quot;"
  case 92 return "\\"
  default return fn:codepoints-to-string($c)
};

(: -------------------------------------------------------------------------- :)
(:
 : DottedRuleSet = hamt(DottedRule)
 : DottedRule = string Category* Category* boolean integer ActionFunction
 :)

declare %private function p:dotted-rule($n,$c,$ws,$f)
{
  p:dotted-rule($n,(),$c,$ws,$f)
};

declare %private function p:dotted-rule($n,$cb,$ca,$ws,$f)
{
  let $h := gr:hash((
      fn:string-to-codepoints($n),
      gr:categories-hash($ca),
      xs:integer($ws)
    )) 
  return function($g) { $g($n,$cb,$ca,$ws,$h,$f) }
};

declare %private function p:dotted-rule-hash($a as item()) as xs:integer { $a(function($n,$cb,$ca,$ws,$h,$f) { $h }) };

declare %private function p:dotted-rule-eq($a as item(), $b as item()) as xs:boolean
{
  $a(function($n1,$cb1,$ca1,$ws1,$h1,$f1) {
    $b(function($n2,$cb2,$ca2,$ws2,$h2,$f2) {
      $n1 eq $n2 and
      $ws1 eq $ws2 and
      gr:categories-eq($ca1,$ca2)
    })
  })
};

declare function p:dotted-ruleset() as item()
{
  hamt:create()
};

declare function p:dotted-ruleset-put(
  $set as item(),
  $dotted-rule
) as item()
{
  hamt:put(p:dotted-rule-hash#1, p:dotted-rule-eq#2, $set, $dotted-rule)
};

declare function p:dotted-ruleset-contains(
  $set as item(),
  $dotted-rule
) as item()
{
  hamt:contains(p:dotted-rule-hash#1, p:dotted-rule-eq#2, $set, $dotted-rule)
};

declare function p:dotted-ruleset-fold(
  $f as function(item()*, item()) as item()*,
  $z as item()*,
  $set as item()
) as item()*
{
  hamt:fold($f,$z,$set)
};

declare function p:dotted-ruleset-hash($set as item()) as xs:integer
{
  gr:hash(
    for $h in p:dotted-ruleset-fold(function($h,$dr) { $h, p:dotted-rule-hash($dr) },(),$set)
    order by $h
    return $h
  )
};

(: -------------------------------------------------------------------------- :)
(:
 : States = array(integer,State) array(state-hash(State),integer) hamt(PendingEdge) array(integer,string)
 : PendingEdge = integer, Category
 : State = DottedRuleSet array(integer,integer) array(integer,integer) (integer,ActionFunction)* integer
 :)

declare %private function p:states-as-string($s)
{
  $s(function($states,$statemap,$pending) {
    fn:string-join((
      for $id in (0 to (sarray:size($states)-1))
      let $state := sarray:get($states,$id)
      return
        $state(function($drs,$nte,$te,$tre,$fns,$h) {
          "State " || $id || " (" || $h || ")",
          dotted-ruleset-fold(function($s,$dr) {
            $s,
            $dr(function($n,$cb,$ca,$ws,$h,$f) {
              "  " || $n || " ::= " ||
              (if(fn:not($ws)) then "ws-explicit(" else "") ||
              fn:string-join($cb ! gr:categories-as-string(.)," ") ||
              "." ||
              fn:string-join($ca ! gr:categories-as-string(.)," ") ||
              (if(fn:not($ws)) then ")" else "")
            })
          },(),$drs),
          sarray:fold(function($s,$nt,$sid) {
            $s, "    edge: " || $nt || " -> " || $sid
          },(),$nte),
          sarray:fold(function($s,$t,$sid) {
            $s, "    edge: '" || codepoint($t) || "' -> " ||
            fn:string-join($sid ! fn:string(.),", ")
          },(),$te),
          for $e in $tre return $e(function($s,$e,$sid) {
            "    edge: [" || codepoint($s) || "-" || codepoint($e) || "] -> " || $sid
          }),
          $fns ! ("    complete: " || fn:head(.()))
        }),
      hamt:fold(function($s,$pe) {
        $s,$pe(function($s,$c) {
          "pending edge state: " || $s || ", category: " || gr:categories-as-string($c)
        })
      },(),$pending)
    ),"&#10;")
  })
};

declare %private function p:states($grammar)
{
  let $states := sarray:create()
  let $statemap := sarray:create()
  let $pending := hamt:create()
  (: let $names := hmap:fold(function($names,$category,$rule) { :)
  (:   sarray:put($names,fn:head($rule),$category) :)
  (: },sarray:create(),$grammar) :)
  return function($f) { $f($states,$statemap,$pending) }
};

declare %private function p:states-get($s,$id)
{
  $s(function($states,$statemap,$pending) {
    sarray:get($states,$id)
  })
};

declare %private function p:states-add-state($s,$grammar,$state,$pe)
{
  $s(function($states,$statemap,$pending) {
    $state(function($drs,$nte,$te,$tre,$fns,$h) {
      let $id := sarray:get($statemap,$h)
      return if(fn:exists($id)) then
        let $states_ := if(fn:empty($pe)) then $states else
          statesarray-add-edge($states,$grammar,$pe,$id)
        let $pending_ := if(fn:empty($pe)) then $pending else
          hamt:delete(pending-edge-hash#1,pending-edge-eq#2,$pending,$pe)
        return ($id,function($f) { $f($states_,$statemap,$pending_) })
      else 
        let $id := sarray:size($states)
        let $states_ := sarray:put($states,$id,$state)
        let $statemap_ := sarray:put($statemap,$h,$id)
        let $states_ := if(fn:empty($pe)) then $states_ else
          statesarray-add-edge($states_,$grammar,$pe,$id)
        let $pending_ := dotted-ruleset-fold(function($p,$dr) {
            $dr(function($n,$cb,$ca,$ws,$h,$f) {
              if(fn:empty($ca)) then $p else
              hamt:put(pending-edge-hash#1,pending-edge-eq#2,$p,pending-edge($id,fn:head($ca)))
            })
          },$pending,$drs)
        let $ws := fn:exists(gr:grammar-get($grammar,$gr:ws-state)) and
          dotted-ruleset-fold(function($b,$dr) {
            $b or $dr(function($n,$cb,$ca,$ws,$h,$f) { $ws }) },fn:false(),$drs)
        let $pending_ := if(fn:not($ws)) then $pending_ else
          hamt:put(pending-edge-hash#1,pending-edge-eq#2,$pending_,
            pending-edge($id,$gr:ws-category))
        let $pending_ := if(fn:empty($pe)) then $pending_ else
          hamt:delete(pending-edge-hash#1,pending-edge-eq#2,$pending_,$pe)
        return ($id,function($f) { $f($states_,$statemap_,$pending_) })
    })
  })
};

declare %private function p:statesarray-add-edge($states,$grammar,$pe,$id)
{
  $pe(function($s,$c) {
    sarray:put($states,$s,state-add-edge(sarray:get($states,$s),$grammar,$c,$id))
  })
};

declare %private function p:states-next-pending-edge($s)
{
  $s(function($states,$statemap,$pending) {
    hamt:fold(function($r,$pe) { $pe },(),$pending)
  })
};

declare %private function p:pending-edge($s,$c) { function($f) { $f($s,$c) } };

declare %private function p:pending-edge-hash($a as item()) as xs:integer
{
  $a(function($s,$c) {
    gr:hash(($s,gr:categories-hash($c)))
  })
};

declare %private function p:pending-edge-eq($a as item(), $b as item()) as xs:boolean
{
  $a(function($s1,$c1) {
    $b(function($s2,$c2) {
      $s1 eq $s2 and
      gr:categories-eq($c1,$c2)
    })
  })
};

declare %private function p:state($grammar,$drs)
{
  let $nte := sarray:create()
  let $te := sarray:create()
  let $tre := ()
  let $cs := fn:distinct-values(dotted-ruleset-fold(function($cs,$dr) {
    $cs,
    $dr(function($n,$cb,$ca,$ws,$h,$f) {
      if(fn:exists($ca)) then () else gr:grammar-get-id($grammar,$n)
    })
  },(),$drs))
  let $fns := for $c in $cs
    return dotted-ruleset-fold(function($r,$dr) {
      $dr(function($n,$cb,$ca,$ws,$h,$f) {
        if(fn:exists($ca) or gr:grammar-get-id($grammar,$n) ne $c) then $r
        else function() { $c, $f }
      })
    },(),$drs)
  let $h := dotted-ruleset-hash($drs)
  return function($f) { $f($drs,$nte,$te,$tre,$fns,$h) }
};

declare %private function p:state-hash($a as item()) as xs:integer { $a(function($drs,$nte,$te,$fns,$h) { $h }) };

declare %private function p:state-eq($a as item(), $b as item()) as xs:boolean
{
  $a(function($drs1,$nte1,$te1,$tre1,$fns1,$h1) {
    $b(function($drs2,$nte2,$te2,$tre2,$fns2,$h2) {
      $h1 eq $h2
    })
  })
};

declare %private function p:te-add($te,$s,$id)
{
  sarray:put($te,$s,($id,sarray:get($te,$s)))
};

declare %private function p:tre-add($tre,$s,$e,$id)
{
  function($f) { $f($s,$e,$id) }, $tre
};

declare %private function p:state-add-edge($state,$grammar,$c,$id)
{
  $state(function($drs,$nte,$te,$tre,$fns,$h) {
    $c(
      (:nt:) function($h,$category) {
        let $cid := gr:grammar-get-id($grammar,$category)
        let $nte := sarray:put($nte,$cid,$id)
        return function($f) { $f($drs,$nte,$te,$tre,$fns,$h) }
      },
      (:t:) function($h,$s) {
        let $te := te-add($te,$s,$id)
        return function($f) { $f($drs,$nte,$te,$tre,$fns,$h) }
      },
      (:tr:) function($h,$s,$e) {
        let $tre := tre-add($tre,$s,$e,$id)
        return function($f) { $f($drs,$nte,$te,$tre,$fns,$h) }
      }
    )
  })
};

(: -------------------------------------------------------------------------- :)

(:
 : Split Epsilon-DFA production
 : http://webhome.cs.uvic.ca/~nigelh/Publications/PracticalEarleyParsing.pdf
 :)

declare %private function p:dfa($grammar)
{
  let $drs := hmap:fold(function($r,$category,$rule) {
    if(fn:head($rule) ne $gr:start-id) then $r
    else gr:ruleset-fold(function($r,$rule){
      $r, $rule(function($c,$ws,$f) { p:dotted-rule($category,$c,$ws,$f) })
    },$r,fn:tail($rule))
  },(),$grammar)
  let $set := fn:fold-left($drs,p:dotted-ruleset(),p:dotted-ruleset-put#2)
  let $states := p:dfa-build-state($grammar,states($grammar),$set,())
  return p:dfa-process-pending($grammar,$states)
};

declare %private function p:dfa-process-pending($grammar,$s)
{
  $s(function($states,$statemap,$pending) {
    let $pe := states-next-pending-edge($s)
    return if(fn:empty($pe)) then $s else
      $pe(function($sid,$c) {
        let $state := sarray:get($states,$sid)
        return $state(function($drs,$nte,$te,$tre,$fns,$h) {
          let $newset := dotted-ruleset-fold(
            dfa-scan($grammar,?,$c,?),dotted-ruleset(),$drs)
          let $newstates := dfa-build-state($grammar,$s,$newset,$pe)
          return dfa-process-pending($grammar,$newstates)
        })
      })
  })
};

declare %private function p:dfa-build-state($grammar,$states,$set,$pe)
{
  let $set := dotted-ruleset-fold(dfa-predict-nullable($grammar,?,?),$set,$set)
  let $r := states-add-state($states,$grammar,state($grammar,$set),$pe)
  let $id := fn:head($r), $states := fn:tail($r)
  let $split-pe := pending-edge($id,$gr:epsilon-category)
  let $split := dotted-ruleset-fold(dfa-predict($grammar,?,?),dotted-ruleset(),$set)
  let $split-empty := dotted-ruleset-fold(function($b,$dr) { fn:false() },fn:true(),$split)
  return if($split-empty) then $states else  
    fn:tail(states-add-state($states,$grammar,state($grammar,$split),$split-pe))
};

declare %private function p:dfa-scan($grammar,$set,$token,$dr)
{
  $dr(function($n,$cb,$ca,$ws,$h,$f) {
    if($ws and gr:categories-eq($gr:ws-category,$token)) then
      dotted-ruleset-put($set,$dr)
    else
    let $category := fn:head($ca)
    return
      if(fn:not(gr:categories-eq($category,$token))) then $set
      else
        let $newdr := dotted-rule($n,($cb,fn:head($ca)),fn:tail($ca),$ws,$f)
        return dotted-ruleset-put($set,$newdr)
  })
};

declare %private function p:dfa-predict-nullable($grammar,$set,$dr)
{        
  fn:fold-left(
    $dr(function($n,$cb,$ca,$ws,$h,$f) {
      for $c1 in fn:head($ca)
      return $c1(
        (:nt:) function($h,$category) {
          if(gr:category-nullable($grammar,$category)) then
            dotted-rule($n,($cb,fn:head($ca)),fn:tail($ca),$ws,$f) else ()
        },
        (:t:) function($h,$s) { () },
        (:tr:) function($h,$s,$e) { () }
      )
    }),
    $set,
    function($set,$newdr) {
      if(dotted-ruleset-contains($set,$newdr)) then $set
      else dfa-predict-nullable($grammar,dotted-ruleset-put($set,$newdr),$newdr)
    }
  )
};

declare %private function p:dfa-predict($grammar,$set,$dr)
{
  fn:fold-left(
    $dr(function($n,$cb,$ca,$ws,$h,$f) {
      if(fn:not($ws)) then () else
        for $rule in gr:grammar-get($grammar,$gr:ws-state)
        return $rule(function($c,$ws,$f) { dotted-rule($gr:ws-state,$c,$ws,$f) }),
      for $c1 in fn:head($ca)
      return $c1(
        (:nt:) function($h,$category) {
          for $rule in gr:grammar-get($grammar,$category)
          return $rule(function($c,$ws,$f) { dotted-rule($category,$c,$ws,$f) })
        },
        (:t:) function($h,$s) { () },
        (:tr:) function($h,$s,$e) { () }
      )
    }),
    $set,
    function($set,$newdr) {
      if(p:dotted-ruleset-contains($set,$newdr)) then $set
      else p:dfa-predict-and-nullable($grammar,p:dotted-ruleset-put($set,$newdr),$newdr)
    }
  )
};

declare %private function p:dfa-predict-and-nullable($grammar,$set,$dr)
{
  fn:fold-left(
    $dr(function($n,$cb,$ca,$ws,$h,$f) {
      if(fn:not($ws)) then () else
        for $rule in gr:grammar-get($grammar,$gr:ws-state)
        return $rule(function($c,$ws,$f) { p:dotted-rule($gr:ws-state,$c,$ws,$f) }),
      for $c1 in fn:head($ca)
      return $c1(
        (:nt:) function($h,$category) {
          if(gr:category-nullable($grammar,$category)) then
            p:dotted-rule($n,($cb,fn:head($ca)),fn:tail($ca),$ws,$f) else (),
          for $rule in gr:grammar-get($grammar,$category)
          return $rule(function($c,$ws,$f) { p:dotted-rule($category,$c,$ws,$f) })
        },
        (:t:) function($h,$s) { () },
        (:tr:) function($h,$s,$e) { () }
      )
    }),
    $set,
    function($set,$newdr) {
      if(p:dotted-ruleset-contains($set,$newdr)) then $set
      else p:dfa-predict-and-nullable($grammar,p:dotted-ruleset-put($set,$newdr),$newdr)
    }
  )
};

(: -------------------------------------------------------------------------- :)

declare function p:make-parser($grammar)
{
  p:make-parser-function($grammar,())
};

declare function p:make-parser($grammar,$options)
{
  if($options = "eval") then util:eval(p:generate-xquery($grammar,("main-module",$options)))
  else p:make-parser-function($grammar,$options)
};

declare %private function p:make-parser-function($grammar,$options)
{
  (: let $_ := $p:log(gr:grammar-as-string($grammar)) :)
  let $grammar := $grammar($p:parse-default-actions)
  let $states := p:dfa($grammar)
  (: let $_ := $p:log(states-as-string($states)) :)
  return p:generate-parser-tables($states)
};

(: -------------------------------------------------------------------------- :)

declare function p:generate-parser-tables($states)
{
  $states(function($states,$statemap,$pending) {
    let $states :=
      for $id in (0 to (sarray:size($states)-1))
      let $state := sarray:get($states,$id)
      return $state(function($drs,$nte,$te,$tre,$fns,$h) {
        pr:state($id,
          (
            sarray:keys($te) ! p:codepoint(.),
            for $e in $tre return $e(function($s,$e,$sid) {
              '[' || p:codepoint($s) || "-" || p:codepoint($e) || ']'
            })
          ),
          sarray:get($nte,?),
          function($c) {
            sarray:get($te,$c),
            for $e in $tre return $e(function($s,$e,$sid) {
              if($s le $c and $c le $e) then $sid else ()
            })
          },
          $fns
        )
      })
    return pr:make-parser($states)
  })
};

declare function p:generate-xquery($grammar)
{
  p:generate-xquery($grammar,())
};

declare function p:generate-xquery($grammar,$options)
{
  let $namespace := $options[fn:starts-with(.,"namespace=")][1] !
    fn:substring-after(.,"namespace=")
  let $namespace := if(fn:exists($namespace) and $namespace ne "") then $namespace
    else "http://snelson.org.uk/functions/parser/generated"
  let $main-module := $options = "main-module"
  (: let $_ := $p:log(gr:grammar-as-string($grammar)) :)
  let $grammar := $grammar($p:generate-default-actions)
  let $states := dfa($grammar)
  (: let $_ := $p:log(states-as-string($states)) :)
  let $moduleURI := fn:replace(try { fn:error() } catch * { $err:module },"^(.*/)[^/]*$","$1") ||
    (if($p:isMarkLogic) then "lib/parser-runtime-ml.xq" else "lib/parser-runtime.xq")
  return fn:string-join(

  $states(function($states,$statemap,$pending) {
    'xquery version "3.0";',
    if($main-module) then (
      'declare namespace x = "' || $namespace || '";'
    ) else (
      'module namespace x = "' || $namespace || '";'
    ),
    "import module namespace p = 'http://snelson.org.uk/functions/parser-runtime' at '" || $moduleURI || "';",
    "declare %private function x:ref($s) { function() { $s } };",

    "declare %private variable $x:states := (&#10;  " ||
    fn:string-join(
      for $id in (0 to (sarray:size($states)-1))
      let $state := sarray:get($states,$id)
      return $state(function($drs,$nte,$te,$tre,$fns,$h) {
        "p:state(" || $id || "," ||

        "(" ||
        fn:string-join((
            sarray:keys($te) ! ('"' || codepoint-xq(.) || '"'),
            for $e in $tre return $e(function($s,$e,$sid) {
              '"[' || codepoint-xq($s) || "-" || codepoint-xq($e) || ']"'
            })
          ),",") ||
        ")" || ",&#10;    " ||

        (if(fn:empty(sarray:keys($nte))) then
          "function($c) { () }"
        else ("function($c) { switch($c)" ||
          fn:string-join(
            for $nt in sarray:keys($nte)
            return " case " || $nt || " return " || sarray:get($nte,$nt),
            "") ||
          " default return () }"
        )) || ",&#10;    " ||

        "function($c) {" || (
          if(fn:empty(sarray:keys($te))) then "" else (
            " switch($c)" ||
            fn:string-join(
              for $t in sarray:keys($te)
              return " case " || $t || " return (" ||
                fn:string-join(sarray:get($te,$t) ! fn:string(.), ",") || ")",
              "") ||
            " default return ()"
          )
        ) || (
          if(fn:empty($tre)) then "" else (
            (if(fn:empty(sarray:keys($te))) then "" else ", ") ||
            fn:string-join(
              for $e in $tre return $e(function($s,$e,$sid) {
                " if(" || $s || " le $c and $c le " || $e || ") then (" ||
                  fn:string-join($sid ! fn:string(.), ",") || ") else ()"
              }), ",")
          )
        ) || (
          if(fn:empty(sarray:keys($te)) and fn:empty($tre)) then " () }"
          else " }"
        ) || ",&#10;    " ||

        "(" ||
        fn:string-join(
          for $f in $fns
          let $c := $f()
          return (
            "&#10;      x:ref((" ||
            fn:string(fn:head($c)) ||
            ",function($ch) {&#10;" ||
            fn:tail($c) ||
            "&#10;      }))"
          )
        ,",") ||
        "))"
      })
    ,",&#10;  ") ||
    ");",
    if($main-module) then (
      "p:make-parser($x:states)"
    ) else (
      "declare %private variable $x:parser := p:make-parser($x:states);",
      "declare function x:parse($s) { $x:parser($s) };"
    )
  }),

  "&#10;")
};
