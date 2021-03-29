const { sum } = require("styp");

const Expr = sum("Expr", {
    Var: ["name"],
    App: ["e1", "e2"],
    Lit: ["type", "val"],
    Lam: ["param", "body"],
    Cond: ["cond", "e1", "e2"],
    Let: ["name","e1","e2"],
    // LetFun: ["name","vars","e"],
    BinOp: ["op","l","r"],
    UnOp: ["op","v"],
    Pair: ["fst","snd"],
    Fix: ["e"]
});

module.exports = {
    Expr
};