const { sum } = require("styp");

// const Lam = (param, type, body) => ({ node: "lambda", param: param, type: type, body: body });
// const Pair = (fst, snd) => ({ node: "pair", fst: fst, snd: snd });
// const Lit = (type, val) => ({ node: "literal", type: type, val: val });
// const Var = (name) => ({ node: "var", name: name });
// const LetB = (name, exp1, exp2) => ({ node: "let", name: name, exp1: exp1, exp2:exp2 });
// const App = (lam, param) => ({ node: "apply", exp1: lam, exp2: param });
// const Condition = (cond, e1, e2) => ({ node: "condition", cond: cond, exp1: e1, exp2: e2 });
// const BinOp = (op, l, r) => ({ node: op, l: l, r: r });
// const UnOp = (op, v) => ({ node: op, val: v });

const Expr = sum("Expr", {
    Var: ["name"],
    App: ["e1", "e2"],
    Lit: ["type", "val"],
    Lam: ["param", "body"],
    Cond: ["cond", "e1", "e2"],
    Let: ["name","e1","e2"],
    LetRec: ["name","vars","e"],
    BinOp: ["op","l","r"],
    UnOp: ["op","v"],
    Pair:["fst","snd"],
    Fix:["e"]
});

module.exports = {
    Expr
};