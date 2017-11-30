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

module namespace gr = "http://snelson.org.uk/functions/grammar";
(: declare default function namespace "http://snelson.org.uk/functions/grammar"; :)
import module namespace hmap = "http://snelson.org.uk/functions/hashmap" at "lib/hashmap.xq";
import module namespace hamt = "http://snelson.org.uk/functions/hamt" at "lib/hamt.xq";

(:
 : Grammar = map(string,Rule)
 : Rule = (integer, RuleSet)
 : RuleSet = hamt(RuleRHS)
 : RuleRHS = Category* boolean ActionFunction
 : ActionFunction = function(item()*) as item()*
 : Category = NT integer string | T integer integer | TR integer integer integer
 :)

declare variable $gr:ws-state := "<ws>";
declare variable $gr:ws-category := gr:category-nt("<ws>");
declare variable $gr:epsilon-state := "<epsilon>";
declare variable $gr:epsilon-category := gr:category-nt("<epsilon>");

declare variable $gr:epsilon-id := 0;
declare variable $gr:ws-id := 1;
declare variable $gr:start-id := 2;

declare variable $gr:ws-option := "ws-explicit";
declare variable $gr:dummy-actions := (
  "",
  "",
  "",
  "",
  function($n) { "" },
  function($n) { "" }
);

(: -------------------------------------------------------------------------- :)

declare %private function gr:category-nt($n)
{
  let $hash := gr:hash((fn:string-to-codepoints($n),0))
  return function($nt,$t,$tr) { $nt($hash,$n) }
};

declare %private function gr:category-t($n)
{
  let $hash := gr:hash((8945782,$n))
  return function($nt,$t,$tr) { $t($hash,$n) }
};

declare %private function gr:category-tr($s,$e)
{
  let $hash := gr:hash((78906239,$s,$e))
  return function($nt,$t,$tr) { $tr($hash,$s,$e) }
};

declare %private function gr:hash-fuse($z,$v) as xs:integer
{
  xs:integer((($z * 5) + $v) mod 4294967296)
};

declare function gr:hash($a as xs:integer*) as xs:integer
{
  fn:fold-left($a,2489012344,gr:hash-fuse#2)
};

declare function gr:categories-hash($a as item()*) as xs:integer
{
  gr:hash($a ! .(
    (:nt:) function($h,$s) { $h },
    (:t:) function($h,$s) { $h },
    (:tr:) function($h,$s,$e) { $h }
  ))
};

declare function gr:categories-eq($a as item()*, $b as item()*) as xs:boolean
{
  fn:count($a) eq fn:count($b) and
  (every $p in fn:map-pairs(function($x,$y) {
      $x(
        (:nt:) function($xh,$xs) {
          $y(
            (:nt:) function($yh,$ys) { $xs eq $ys },
            (:t:) function($yh,$ys) { fn:false() },
            (:tr:) function($yh,$ys,$ye) { fn:false() }
          )
        },
        (:t:) function($xh,$xs) {
          $y(
            (:nt:) function($yh,$ys) { fn:false() },
            (:t:) function($yh,$ys) { $xs eq $ys },
            (:tr:) function($yh,$ys,$ye) { fn:false() }
          )
        },
        (:tr:) function($xh,$xs,$xe) {
          $y(
            (:nt:) function($yh,$ys) { fn:false() },
            (:t:) function($yh,$ys) { fn:false() },
            (:tr:) function($yh,$ys,$ye) { $xs eq $ys and $xe eq $ye }
          )
        }
      )
    },$a,$b) satisfies $p)
};

declare %private function gr:rulerhs($categories,$ws,$f)
{
  function($g) { $g($categories,$ws,$f) }
};

declare %private function gr:rulerhs-hash($a as item()) as xs:integer
{
  $a(function($c,$ws,$f) {
    gr:hash((gr:categories-hash($c),xs:integer($ws)))
  })
};

declare %private function gr:rulerhs-eq($a as item(), $b as item()) as xs:boolean
{
  $a(function($ac,$aws,$af) {
    $b(function($bc,$bws,$bf) {
      gr:categories-eq($ac,$bc) and $aws eq $bws
    })
  })
};

declare %private function gr:ruleset() as item()
{
  hamt:create()
};

declare %private function gr:ruleset-put(
  $set as item(),
  $rule
) as item()
{
  hamt:put(gr:rulerhs-hash#1,gr:rulerhs-eq#2,$set,$rule)
};

declare function gr:ruleset-fold(
  $f as function(item()*, item()*) as item()*,
  $z as item()*,
  $set as item()
) as item()*
{
  hamt:fold($f,$z,$set)
};

(: -------------------------------------------------------------------------- :)

(:
 : Grammar construction functions
 :)

declare %private function gr:codepoint($c)
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

declare function gr:categories-as-string($cs)
{
  for $c in fn:head($cs)
  return $c(
    (:nt:) function($h,$s) {
      $s,
      gr:categories-as-string(fn:tail($cs))
    },
    (:t:) function($h,$s) {
      let $r := gr:combine-terminals-as-string(fn:tail($cs))
      return (
        ('"' || gr:codepoint($s) || fn:head($r) || '"'),
        gr:categories-as-string(fn:tail($r))
      )
    },
    (:tr:) function($h,$s,$e) {
      "[" || gr:codepoint($s) || "-" || gr:codepoint($e) || "]",
      gr:categories-as-string(fn:tail($cs))
    }
  )
};

declare %private function gr:combine-terminals-as-string($cs)
{
  for $c in fn:head($cs)
  return $c(
    (:nt:) function($h,$s) { "", $cs },
    (:t:) function($h,$s) {
      let $r := gr:combine-terminals-as-string(fn:tail($cs))
      return ((gr:codepoint($s) || fn:head($r)), fn:tail($r))
    },
    (:tr:) function($h,$s,$e) { "", $cs }
  )
};


declare function gr:grammar-as-string($grammar)
{
  let $grammar := $grammar($gr:dummy-actions)
  return fn:string-join(
    for $r in hmap:fold(function($z,$n,$rule) { $z,function() { $n,$rule } },(),$grammar)
    let $r_ := $r()
    let $n := fn:head($r_)
    let $r_ := fn:tail($r_)
    let $id := fn:head($r_)
    let $ruleset := fn:tail($r_)
    where $id ne $gr:epsilon-id
    order by $id
    return (
      "(" || $id || ") " || $n || " ::= " ||
      fn:string-join(
        gr:ruleset-fold(function($s,$rule) {
          $s,
          $rule(function($c,$ws,$f) {
            (if(fn:not($ws)) then "ws-explicit(" else "") ||
            fn:string-join(gr:categories-as-string($c)," ") ||
            (if(fn:not($ws)) then ")" else "")
          })
        },(),$ruleset),
      " | ")
    ),
  "&#10;")
};

declare %private function gr:make-rules($n,$i,$c,$r,$ws,$f,$df)
{
  if(fn:empty($r)) then ($i,function($g) { $g($n,$c,$ws,$f) })
  else fn:head($r)($n,$i,$c,fn:tail($r),$ws,$f,$df)
};

declare %private function gr:chain($i,$fns)
{
  if(fn:empty($fns)) then $i else
  let $r1 := fn:head($fns)($i)
  let $r2 := gr:chain(fn:head($r1),fn:tail($fns))
  return (fn:head($r2),fn:tail($r1),fn:tail($r2))
};

declare function gr:codepoint-range($start,$end)
{
  function($n,$i,$c,$r,$ws,$f,$df) {
    gr:make-rules($n,$i,($c,gr:category-tr($start,$end)),$r,$ws,$f,$df)
  }
};

declare function gr:char-range($start_,$end_)
{
  let $start := fn:string-to-codepoints($start_) treat as xs:integer
  let $end := fn:string-to-codepoints($end_) treat as xs:integer
  return gr:codepoint-range($start,$end)
};

declare function gr:term($value)
{
  function($n,$i,$c,$r,$ws,$f,$df) {
    if(fn:string-length($value) eq 1 or fn:not($ws)) then (
      gr:make-rules($n,$i,($c,fn:string-to-codepoints($value) ! gr:category-t(.)),$r,$ws,$f,$df)
    ) else (
      let $n_ := $n || "_" || $i
      let $nt := gr:non-term($n_)
      return (
        gr:make-rules($n,$i+1,$c,($nt,$r),$ws,$f,$df),
        fn:tail(gr:make-rules($n_,1,fn:string-to-codepoints($value) ! gr:category-t(.),(),fn:false(),
          $df[2],$df))
      )
    )
  }
};

declare function gr:term-($value)
{
  function($n,$i,$c,$r,$ws,$f,$df) {
    let $n_ := $n || "_" || $i
let $lll := util:log-app('TRACE','apps.nabu',($value,$n_))
    let $nt := gr:non-term($n_)
    return (
      gr:make-rules($n,$i+1,$c,($nt,$r),$ws,$f,$df),
      fn:tail(gr:make-rules($n_,1,fn:string-to-codepoints($value) ! gr:category-t(.),(),fn:false(),
        $df[1],$df))
    )
  }
};

declare function gr:non-term($value)
{
    let $v := util:log-system-out(if ($value) then $value else 'empty')
    return
  function($n,$i,$c,$r,$ws,$f,$df) {
    gr:make-rules($n,$i,($c,gr:category-nt($value)),$r,$ws,$f,$df)
  }
};

declare function gr:non-term-($value)
{
  function($n,$i,$c,$r,$ws,$f,$df) {
    let $n_ := $n || "_" || $i
    let $nt := gr:non-term($n_)
    return (
      gr:make-rules($n,$i+1,$c,($nt,$r),$ws,$f,$df),
      fn:tail(gr:make-rules($n_,1,gr:category-nt($value),(),$ws,$df[1],$df))
    )
  }
};

declare function gr:non-term-attr($value)
{
  function($n,$i,$c,$r,$ws,$f,$df) {
    let $n_ := $n || "_" || $i
    let $nt := gr:non-term($n_)
    return (
      gr:make-rules($n,$i+1,$c,($nt,$r),$ws,$f,$df),
      fn:tail(gr:make-rules($n_,1,gr:category-nt($value),(),$ws,$df[6]($value),$df))
    )
  }
};

declare function gr:optional($b)
{
  let $b_ := gr:make-non-terms($b)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    gr:chain($i,(
      gr:make-rules($n,?,$c,$r,$ws,$f,$df),
      gr:make-rules($n,?,$c,($b_,$r),$ws,$f,$df)
    ))
  }
};

declare function gr:one-or-more($b)
{
  gr:one-or-more($b,())
};

declare function gr:one-or-more($b,$s)
{
  let $b_ := gr:make-non-terms($b)
  let $s_ := gr:make-non-terms($s)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    let $n_ := $n || "_" || $i
    let $nt := gr:non-term($n_)
    return (
      gr:make-rules($n,$i+1,$c,($nt,$r),$ws,$f,$df),
      fn:tail(gr:chain(1,(
        gr:make-rules($n_,?,(),$b_,$ws,$df[4],$df),
        gr:make-rules($n_,?,(),($nt,$s_,$b_),$ws,$df[4],$df)
      )))
    )
  }
};

declare function gr:zero-or-more($b)
{
  let $b_ := gr:make-non-terms($b)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    let $n_ := $n || "_" || $i
    let $nt := gr:non-term($n_)
    return (
      gr:make-rules($n,$i+1,$c,($nt,$r),$ws,$f,$df),
      fn:tail(gr:chain(1,(
        gr:make-rules($n_,?,(),(),$ws,$df[4],$df),
        gr:make-rules($n_,?,(),($nt,$b_),$ws,$df[4],$df)
      )))
    )
  }
};

declare function gr:zero-or-more($b,$s)
{
  if(fn:empty($s)) then gr:zero-or-more($b)
  else gr:optional(gr:one-or-more($b,$s))
};

declare function gr:sequence($b)
{
  let $b_ := gr:make-non-terms($b)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    gr:make-rules($n,$i,$c,($b_,$r),$ws,$f,$df)
  }
};

declare function gr:choice($b1,$b2)
{
  let $b1_ := gr:make-non-terms($b1)
  let $b2_ := gr:make-non-terms($b2)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    gr:chain($i,(
      gr:make-rules($n,?,$c,($b1_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b2_,$r),$ws,$f,$df)
    ))
  }
};

declare function gr:choice($b1,$b2,$b3)
{
  let $b1_ := gr:make-non-terms($b1)
  let $b2_ := gr:make-non-terms($b2)
  let $b3_ := gr:make-non-terms($b3)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    gr:chain($i,(
      gr:make-rules($n,?,$c,($b1_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b2_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b3_,$r),$ws,$f,$df)
    ))
  }
};

declare function gr:choice($b1,$b2,$b3,$b4)
{
  let $b1_ := gr:make-non-terms($b1)
  let $b2_ := gr:make-non-terms($b2)
  let $b3_ := gr:make-non-terms($b3)
  let $b4_ := gr:make-non-terms($b4)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    gr:chain($i,(
      gr:make-rules($n,?,$c,($b1_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b2_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b3_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b4_,$r),$ws,$f,$df)
    ))
  }
};

declare function gr:choice($b1,$b2,$b3,$b4,$b5)
{
  let $b1_ := gr:make-non-terms($b1)
  let $b2_ := gr:make-non-terms($b2)
  let $b3_ := gr:make-non-terms($b3)
  let $b4_ := gr:make-non-terms($b4)
  let $b5_ := gr:make-non-terms($b5)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    gr:chain($i,(
      gr:make-rules($n,?,$c,($b1_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b2_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b3_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b4_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b5_,$r),$ws,$f,$df)
    ))
  }
};

declare function gr:choice($b1,$b2,$b3,$b4,$b5,$b6)
{
  let $b1_ := gr:make-non-terms($b1)
  let $b2_ := gr:make-non-terms($b2)
  let $b3_ := gr:make-non-terms($b3)
  let $b4_ := gr:make-non-terms($b4)
  let $b5_ := gr:make-non-terms($b5)
  let $b6_ := gr:make-non-terms($b6)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    gr:chain($i,(
      gr:make-rules($n,?,$c,($b1_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b2_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b3_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b4_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b5_,$r),$ws,$f,$df),
      gr:make-rules($n,?,$c,($b6_,$r),$ws,$f,$df)
    ))
  }
};

declare function gr:nchoice($b)
{
  let $b_ := gr:make-non-terms($b)
  return function($n,$i,$c,$r,$ws,$f,$df) {
    gr:chain($i, $b_ ! gr:make-rules($n,?,$c,(.,$r),$ws,$f,$df))
  }
};

declare %private function gr:make-non-terms($categories)
{
  for $c in $categories
  return typeswitch($c)
    case xs:string return gr:non-term($c)
    default return $c
};

declare function gr:rule($n,$categories)
{
  gr:rule($n,$categories,())
};

declare function gr:rule-($n,$categories)
{
  gr:rule-($n,$categories,())
};

declare function gr:rule-attr($n,$categories)
{
  gr:rule-attr($n,$categories,())
};

declare function gr:rule($n,$categories,$options)
{
  let $ws := fn:not($options = $gr:ws-option)
  return function($df) {
    fn:tail(gr:make-rules($n,1,(),gr:make-non-terms($categories),$ws,$df[5]($n),$df))
  }
};

declare function gr:rule-($n,$categories,$options)
{
  let $ws := fn:not($options = $gr:ws-option)
  return function($df) {
    fn:tail(gr:make-rules($n,1,(),gr:make-non-terms($categories),$ws,$df[4],$df))
  }
};

declare function gr:rule-attr($n,$categories,$options)
{
  let $ws := fn:not($options = $gr:ws-option)
  return function($df) {
    fn:tail(gr:make-rules($n,1,(),gr:make-non-terms($categories),$ws,$df[6]($n),$df))
  }
};

declare function gr:rule($n,$categories,$options,$f)
{
  let $ws := fn:not($options = $gr:ws-option)
  return function($df) {
    fn:tail(gr:make-rules($n,1,(),gr:make-non-terms($categories),$ws,$f,$df))
  }
};

declare function gr:token($n,$categories)
{
  function($df) {
    fn:tail(gr:make-rules($n,1,(),gr:make-non-terms($categories),fn:false(),$df[3],$df))
  }
};

declare function gr:token-($n,$categories)
{
  function($df) {
    fn:tail(gr:make-rules($n,1,(),gr:make-non-terms($categories),fn:false(),$df[1],$df))
  }
};

declare function gr:ws($n,$categories)
{
  function($df) {
    gr:rule($n,$categories,$gr:ws-option,$df[1])($df),
    gr:rule($gr:ws-state,$n,$gr:ws-option,$df[1])($df)
  }
};

declare function gr:ws($n,$categories,$f)
{
  function($df) {
    gr:rule($n,$categories,$gr:ws-option,$f)($df),
    gr:rule($gr:ws-state,$n,$gr:ws-option,$df[1])($df)
  }
};

declare function gr:grammar($rules)
{
  gr:grammar($rules,?)
};

declare %private function gr:grammar($rules,$df)
{
let $lll := util:log-app('TRACE','apps.nabu',count($rules))
let $lll := util:log-app('TRACE','apps.nabu',count($df))
  let $rules := $rules ! .($df)
let $lll := util:log-app('TRACE','apps.nabu',"post")
let $lll := util:log-app('TRACE','apps.nabu',$rules)
  let $map := fn:fold-left(
    $rules,
    hmap:create(),
    function($map,$rule) {
      $rule(function($category,$categories,$ws,$f) {
        let $rule := hmap:get($map,$category)
        let $id :=
          if($category eq $gr:ws-state) then $gr:ws-id
          else if(fn:exists($rule)) then fn:head($rule)
          else (hmap:count($map) + $gr:start-id)
        let $set := if(fn:exists($rule)) then fn:tail($rule) else gr:ruleset()
        return hmap:put($map,$category,($id,gr:ruleset-put($set,gr:rulerhs($categories,$ws,$f))))
      })
    }
  )
  return hmap:put($map,$gr:epsilon-state,($gr:epsilon-id))
};

declare function gr:grammar-get($grammar,$category)
{
  let $rule := hmap:get($grammar,$category)
  where fn:exists($rule)
  return gr:ruleset-fold(function($s,$c){ $s,$c },(),fn:tail($rule))
};

declare function gr:grammar-get-id($grammar,$category)
{
  let $rule := hmap:get($grammar,$category)
  where fn:exists($rule)
  return fn:head($rule)
};

declare function gr:category-nullable($grammar,$category)
{
  gr:category-nullable($grammar,$category,())
};

declare %private function gr:category-nullable($grammar,$category,$searched)
{
  if($category = $searched) then fn:true() else
  some $rule in gr:grammar-get($grammar,$category)
  satisfies
    (every $rc in $rule(function($c,$ws,$f) { $c }) satisfies $rc(
      (:nt:) function($h,$s) { fn:true() },
      (:t:) function($h,$s) { fn:false() },
      (:tr:) function($h,$s,$e) { fn:false() }
    )) and
    (every $rc in $rule(function($c,$ws,$f) { $c }) satisfies $rc(
      (:nt:) function($h,$s) { gr:category-nullable($grammar,$s,($searched,$category)) },
      (:t:) function($h,$s) { fn:false() },
      (:tr:) function($h,$s,$e) { fn:false() }
    ))
};
