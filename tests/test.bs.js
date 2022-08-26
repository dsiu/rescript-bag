// Generated by ReScript, PLEASE EDIT WITH CARE

import * as Curry from "rescript/lib/es6/curry.js";
import * as Random from "rescript/lib/es6/random.js";
import * as Bag$Bag from "../src/bag.bs.js";
import * as Caml_obj from "rescript/lib/es6/caml_obj.js";

var compare = Caml_obj.compare;

var I = {
  compare: compare
};

var B = Bag$Bag.Make(I);

var a = Curry._3(B.add, 1, 1, Curry._3(B.add, 2, 2, Curry._3(B.add, 3, 3, B.empty)));

var b = Curry._3(B.add, 1, 4, Curry._3(B.add, 2, 5, Curry._3(B.add, 3, 6, B.empty)));

if (Curry._1(B.cardinal, a) !== 6) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          11,
          2
        ],
        Error: new Error()
      };
}

if (Curry._1(B.cardinal, Curry._2(B.sum, a, b)) !== 21) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          12,
          2
        ],
        Error: new Error()
      };
}

if (Curry._1(B.cardinal, Curry._2(B.union, a, b)) !== 15) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          13,
          2
        ],
        Error: new Error()
      };
}

if (!Curry._1(B.is_empty, Curry._2(B.diff, a, b))) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          14,
          2
        ],
        Error: new Error()
      };
}

if (Curry._1(B.cardinal, Curry._2(B.diff, b, a)) !== 9) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          15,
          2
        ],
        Error: new Error()
      };
}

if (!Curry._2(B.equal, Curry._2(B.inter, a, b), a)) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          16,
          2
        ],
        Error: new Error()
      };
}

if (!Curry._2(B.included, a, b)) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          17,
          2
        ],
        Error: new Error()
      };
}

if (Curry._2(B.included, b, a)) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          18,
          2
        ],
        Error: new Error()
      };
}

if (Curry._2(B.disjoint, b, a)) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          19,
          2
        ],
        Error: new Error()
      };
}

if (!Caml_obj.equal(Curry._1(B.elements, a), {
        hd: [
          1,
          1
        ],
        tl: {
          hd: [
            2,
            2
          ],
          tl: {
            hd: [
              3,
              3
            ],
            tl: /* [] */0
          }
        }
      })) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          20,
          2
        ],
        Error: new Error()
      };
}

if (!Caml_obj.equal(Curry._1(B.min_elt, a), [
        1,
        1
      ])) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          21,
          2
        ],
        Error: new Error()
      };
}

if (!Caml_obj.equal(Curry._1(B.max_elt, a), [
        3,
        3
      ])) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          22,
          2
        ],
        Error: new Error()
      };
}

function f(param) {
  return 1;
}

if (Curry._1(B.cardinal, Curry._2(B.map, f, a)) !== 3) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          24,
          2
        ],
        Error: new Error()
      };
}

if (Curry._1(B.cardinal, Curry._2(B.map, f, b)) !== 3) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          25,
          2
        ],
        Error: new Error()
      };
}

var e = Curry._2(B.filter, (function (x, param) {
        return x % 2 === 0;
      }), a);

if (!Caml_obj.equal(Curry._1(B.min_elt, e), [
        2,
        2
      ])) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          27,
          2
        ],
        Error: new Error()
      };
}

if (!Caml_obj.equal(Curry._1(B.max_elt, e), [
        2,
        2
      ])) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          28,
          2
        ],
        Error: new Error()
      };
}

if (!Caml_obj.equal(Curry._1(B.choose, e), [
        2,
        2
      ])) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          29,
          2
        ],
        Error: new Error()
      };
}

if (Curry._1(B.cardinal, e) !== 2) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          30,
          2
        ],
        Error: new Error()
      };
}

var o = Curry._2(B.filter, (function (x, param) {
        return x % 2 === 1;
      }), b);

if (!Caml_obj.equal(Curry._1(B.min_elt, o), [
        1,
        4
      ])) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          33,
          2
        ],
        Error: new Error()
      };
}

if (!Caml_obj.equal(Curry._1(B.max_elt, o), [
        3,
        6
      ])) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          34,
          2
        ],
        Error: new Error()
      };
}

if (Curry._1(B.cardinal, o) !== 10) {
  throw {
        RE_EXN_ID: "Assert_failure",
        _1: [
          "test.ml",
          35,
          2
        ],
        Error: new Error()
      };
}

function test(n) {
  var b1 = B.empty;
  var b2 = B.empty;
  for(var x = 0; x <= n; ++x){
    b1 = Curry._3(B.add, x, 2, b1);
    if (Curry._1(B.cardinal, b1) !== ((x + 1 | 0) << 1)) {
      throw {
            RE_EXN_ID: "Assert_failure",
            _1: [
              "test.ml",
              43,
              4
            ],
            Error: new Error()
          };
    }
    b2 = Curry._3(B.add, n - x | 0, undefined, b2);
    if (Curry._1(B.cardinal, b2) !== ((x << 1) + 1 | 0)) {
      throw {
            RE_EXN_ID: "Assert_failure",
            _1: [
              "test.ml",
              45,
              4
            ],
            Error: new Error()
          };
    }
    b2 = Curry._3(B.add, n - x | 0, undefined, b2);
    if (x < (n / 2 | 0) && !Curry._2(B.disjoint, b1, b2)) {
      throw {
            RE_EXN_ID: "Assert_failure",
            _1: [
              "test.ml",
              47,
              20
            ],
            Error: new Error()
          };
    }
    
  }
  if (!Curry._2(B.mem, n, b1)) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            49,
            2
          ],
          Error: new Error()
        };
  }
  if (Curry._2(B.occ, n, b1) !== 2) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            50,
            2
          ],
          Error: new Error()
        };
  }
  if (Curry._1(B.cardinal, b1) !== ((n + 1 | 0) << 1)) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            51,
            2
          ],
          Error: new Error()
        };
  }
  if (Curry._1(B.cardinal, b2) !== ((n + 1 | 0) << 1)) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            52,
            2
          ],
          Error: new Error()
        };
  }
  if (!Curry._2(B.equal, b1, b2)) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            53,
            2
          ],
          Error: new Error()
        };
  }
  if (!Curry._2(B.for_all, (function (x, param) {
            return x <= n;
          }), b1)) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            54,
            2
          ],
          Error: new Error()
        };
  }
  if (Curry._2(B.for_all, (function (x, param) {
            return x < n;
          }), b1)) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            55,
            2
          ],
          Error: new Error()
        };
  }
  if (!Curry._2(B.exists, (function (x, m) {
            if (x === 0) {
              return m === 2;
            } else {
              return false;
            }
          }), b2)) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            56,
            2
          ],
          Error: new Error()
        };
  }
  for(var x$1 = 0; x$1 <= n; ++x$1){
    b1 = Curry._2(B.remove_all, x$1, b1);
    b2 = Curry._3(B.remove, n - x$1 | 0, 2, b2);
  }
  if (!Curry._1(B.is_empty, b1)) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            61,
            2
          ],
          Error: new Error()
        };
  }
  if (!Curry._1(B.is_empty, b2)) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            62,
            2
          ],
          Error: new Error()
        };
  }
  
}

for(var n = 0; n <= 10; ++n){
  test(Math.imul(10, n));
}

Random.init(42);

function test$1(n) {
  var b1 = B.empty;
  var b2 = B.empty;
  for(var i = 0; i < n; ++i){
    b1 = Curry._3(B.add, i, Random.$$int(10), b1);
    b2 = Curry._3(B.add, i, Random.$$int(3), b2);
  }
  var match = Curry._2(B.div, b1, b2);
  if (!Curry._2(B.equal, b1, Curry._2(B.sum, Curry._2(B.mul, b2, match[0]), match[1]))) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            82,
            2
          ],
          Error: new Error()
        };
  }
  var match$1 = Curry._2(B.divi, b1, 1);
  if (!(Curry._2(B.equal, match$1[0], b1) && Curry._1(B.is_empty, match$1[1]))) {
    throw {
          RE_EXN_ID: "Assert_failure",
          _1: [
            "test.ml",
            84,
            2
          ],
          Error: new Error()
        };
  }
  for(var k = 2; k <= 5; ++k){
    var match$2 = Curry._2(B.divi, b1, k);
    if (!Curry._2(B.equal, b1, Curry._2(B.sum, Curry._2(B.mul, match$2[0], k), match$2[1]))) {
      throw {
            RE_EXN_ID: "Assert_failure",
            _1: [
              "test.ml",
              87,
              4
            ],
            Error: new Error()
          };
    }
    
  }
}

for(var n$1 = 0; n$1 <= 10; ++n$1){
  test$1(n$1);
}

export {
  I ,
  B ,
  test$1 as test,
}
/* B Not a pure module */
