// Type checker
// Based on http://dev.stephendiehl.com/fun/006_hindley_milner.html
const { sum } = require("styp");
const { equal } = require("saman");

const uops = ["NEG","NOT"];
const bops = ["ADD", "SUB", "DIV", "MUL", "AND", "OR", "GT", "LT", "EQ"];

// Type Defs
const Type = sum("Types", {
    TVar: ["v"],
    TCon: ["name"],
    TPair: ["p1", "p2"],
    TArr: ["t1", "t2"]
});

const Scheme = sum("Scheme", {
    Forall: ["var", "type"]
});

const TInt = Type.TCon("int");
const TBool = Type.TCon("bool");
const TUnit = Type.TCon("unit");

const optypes = {
    "ADD": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "MUL": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "SUB": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "DIV": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "AND": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "OR": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "GT": Type.TArr(TInt,Type.TArr(TInt,TBool)),
    "LT": Type.TArr(TInt,Type.TArr(TInt,TBool)),
    "NOT": Type.TArr(TBool,TBool),
    "NEG": Type.TArr(TInt,TInt),
    "EQ": Scheme.Forall(
        [Type.TVar("o1"),Type.TVar("o2")],
        Type.TArr(Type.TVar("o1"),Type.TArr(Type.TVar("o2"),TBool))
    )
}

function printType(type) {
    if(Type.TCon.is(type)) return type.name;
    if(Type.TVar.is(type)) return type.v;
    if(Type.TArr.is(type)) return `(${printType(type.t1)} -> ${printType(type.t2)})`
    if(Scheme.Forall.is(type)) 
        return type.var.length?`forall ${type.var.map(e => printType(e)).join(" ")}. ${printType(type.type)}`:printType(type.type);
}

// temp
const Lam = (param, type, body) => ({ node: "lambda", param: param, type: type, body: body });
const Pair = (fst, snd) => ({ node: "pair", fst: fst, snd: snd });
const Lit = (type, val) => ({ node: "literal", type: type, val: val });
const Var = (name) => ({ node: "var", name: name });
const LetB = (name, exp1, exp2) => ({ node: "let", name: name, exp1: exp1, exp2:exp2 });
const App = (lam, param) => ({ node: "apply", exp1: lam, exp2: param });
const Condition = (cond, e1, e2) => ({ node: "condition", cond: cond, exp1: e1, exp2: e2 });
const BinOp = (op, l, r) => ({ node: op, l: l, r: r });
const UnOp = (op, v) => ({ node: op, val: v });

// Work in progress
const Expr = sum("Expr", {
    Var: ["name"],
    App: ["e1", "e2"],
    Lit: ["type", "val"],
    Lam: ["param", "body"],
    Cond: ["cond", "e1", "e2"],
    Let: ["exp1","exp2"],
    BinOp: ["op","l","r"],
    UnOp: ["op","val"]
});

// const Constraint = tagged("ConstraintEq",["left","right"]);

// Errors
const genericError = (msg) => { throw new Error(msg) };
const notInScope = (name) => genericError(`Variable: '${name}' not in Scope`);
const defInScope = (name) => genericError(`Cannot redefine Variable: '${name}'`);
const notUnifiable = (type1, type2, msg = "") => genericError(`Cannot unify types: ${printType(type1)} with ${printType(type2)} ${msg}`);
const failedOccursCheck = (v,name) => genericError(`Failed Occurs Check: ${printType(v)} in ${printType(name)}`);

class TypeEnv {
    constructor(parent) {
        this.env = {};
        this.parent = parent;
    }

    exists(name) {
        if (this.env[name]) return this.env[name];
        else if (this.parent) return this.parent.lookUp(name);
        return false;
    }

    addBinding(name, type) {
        this.env[name] = type
    }

    removeBinding(name) {
        delete this.env[name]
    }

    lookUp(name) {  
        if (this.env[name]) return this.env[name];
        if (this.parent) return this.parent.lookUp(name);
        notInScope(name);
    }
}

class TypeChecker {
    constructor() {
        this.env = new TypeEnv(null);
        this.subst = {};
        this.varInit();
        // this.constraints = [];
    }

    varInit() {
        this.names = {};
        this.count = 0;
        for(let i = "a".charCodeAt(0);i < "z".charCodeAt(0);i++) {
            this.names[i-97] = [String.fromCharCode(i),0];
        }
    }

    fresh() {
        const pair = this.names[this.count++ % 27];
        return Type.TVar(`${pair[0]}${pair[1]?pair[1]:""}`);
    }

    lookUp(name,env) {
        const t = env.lookUp(name);
        return Scheme.Forall.is(t) ? this.instantiate(t) : t;
    }

    // addConstraint(type1,type2) {
    //     this.constraints.push(Constraint(type1,type2));
    // }

    occursCheck(v, t, subst) {
        if (equal(v, t)) return true;
        if (Type.TVar.is(t) && t.v in subst)
            return this.occursCheck(v, subst[t.v], subst);
        if (Type.TArr.is(t))
            return this.occursCheck(v, t.t1, subst) || this.occursCheck(v, t.t2, subst);
        return false;
    }

    unifyVar(v, t, subst) {
        if (v.v in subst) return this.unify(subst[v.v], t, subst);
        if (Type.TVar.is(t) && t.v in subst) return this.unify(v, subst[t.v], subst);
        if (this.occursCheck(v, t, subst)) failedOccursCheck(v,t);
        else {
            subst[v.v] = t;
            return subst;
        }
    }

    unify(t1, t2, subst = this.subst) {
        if (equal(t1, t2)) return subst;
        if (Type.TVar.is(t1)) return this.unifyVar(t1, t2, subst);
        if (Type.TVar.is(t2)) return this.unifyVar(t2, t1, subst);
        if (Type.TArr.is(t1) && Type.TArr.is(t2)) {
            subst = this.unify(t1.t1, t2.t1, subst);
            return this.unify(t1.t2, t2.t2, subst);
        }
        notUnifiable(t1, t2);
    }

    apply(typ, subst = this.subst) {
        if (!subst) return null;
        if (Object.keys(subst).length == 0) return typ;
        if (equal(typ, TInt) || equal(typ, TBool)) return typ;
        if (Type.TVar.is(typ))
            return typ.v in subst? this.apply(subst[typ.v], subst):typ;
        if (Type.TArr.is(typ))
            return Type.TArr(
                this.apply(typ.t1, subst),
                this.apply(typ.t2, subst)
            );
        if (Scheme.Forall.is(typ)) {
            typ.var.forEach(v => delete subst[v.v]);
            return Scheme.Forall(typ.var, this.apply(typ.type, subst));
        }
        return null;
    }

    applyEnv(env, subst=this.subst) {
        for(let t in env.env) {
            env.env[t] = this.apply(env.env[t],subst);
        }
        if(env.parent) this.applyEnv(env.parent,subst);
        return env;
    }

    ftv(type) {
        if (Type.TCon.is(type)) return new Set();
        if (Type.TVar.is(type)) return new Set([type.v]);
        if (Type.TArr.is(type)) return new Set([...this.ftv(type.t1), ...this.ftv(type.t2)]);
        if (Scheme.Forall.is(type)) {
            const bounded = new Set(type.var.map(v => v.v));
            return new Set([...(this.ftv(type.type))].filter(v => !bounded.has(v)));
        }
        return null;
    }

    ftvEnv(env) {
        const curr = Object.values(env.env).map(t => Array.from(this.ftv(t)));
        if(env.parent) curr.push([...(this.ftvEnv(env.parent))]);
        return new Set(curr.flat());
    }

    instantiate(type) {
        const ns = {}
        type.var.map(v => ns[v.v] = this.fresh());
        return this.apply(type.type, ns);
    }

    generalize(type, env) {
        // new Set(Object.values(env.env).map(t => Array.from(this.ftv(t))).flat());
        const enftv = this.ftvEnv(env);
        const as = new Set([...(this.ftv(type))].filter(v => !enftv.has(v)));
        return Scheme.Forall([...as].map(v => Type.TVar(v)), type);
    }

    infer(ast, env = this.env) {
        if (ast.node == "literal")
            return ast.type == "int" ? TInt : TBool;
        else if (ast.node == "var") 
            return  this.lookUp(ast.name,env);
        else if (ast.node == "let") {
            if (env.exists(ast.name)) defInScope(ast.name);
            const t1 = this.infer(ast.exp1,env);
            const tdash = this.generalize(t1,this.applyEnv(env,this.subst));
            env.addBinding(ast.name,tdash);
            return ast.exp2?this.infer(ast.exp2,env):tdash;
        }
        else if (ast.node == "condition") {
            const cond = this.infer(ast.cond, env);
            const t1 = this.infer(ast.exp1, env);
            const t2 = this.infer(ast.exp2, env);
            this.unify(cond, TBool);
            this.unify(t1, t2);
            return this.apply(t1);
        }
        else if (ast.node == "lambda") {
            const tv = this.fresh();
            const ne = new TypeEnv(env);
            ne.addBinding(ast.param, Scheme.Forall([],tv));
            const body = this.infer(ast.body, ne);
            return this.apply(Type.TArr(tv, body));
        }
        else if (ast.node == "apply") {
            const t1 = this.infer(ast.exp1, env);
            const t2 = this.infer(ast.exp2, this.applyEnv(env));
            const tv = this.fresh();
            this.unify(this.apply(t1), Type.TArr(t2, tv));
            return this.apply(tv);
        }
        else if(ast.node == "fix") {
            const t = this.infer(e,env);
            const tv = this.fresh();
            this.unify(Type.TArr(tv,tv),t);
            return this.apply(tv);
        }
        else if(uops.includes(ast.node)) {
            const t = this.infer(ast.val,env);
            const tv = this.fresh();
            this.unify(Type.TArr(t,tv),optypes[ast.node]);
            return this.apply(tv);
        }
        else if(bops.includes(ast.node)) {
            const t1 = this.infer(ast.l,env);
            const t2 = this.infer(ast.r,env);
            const tv = this.fresh();
            let op = optypes[ast.node];
            if(Scheme.Forall.is(op)) op = this.instantiate(op);
            this.unify(Type.TArr(t1,Type.TArr(t2,tv)),op);
            return this.apply(tv);
        }
        genericError("Unrecognized AST Node");
    }

    getType(name) {
        return printType(this.env.lookUp(name));
    }

    getTypeEnv() {
        return Object.keys(this.env.env).map(k => `${k} :: ${this.getType(k)}`)
    }

    valid(ast) {
        this.varInit();
        this.subst = {};
        return printType(this.infer(ast));
    }
}



const tc1 = new TypeChecker();
// let code = Lam("x", null, Var("x"));
let code2 = LetB("fst",Lam("x",null,Lam("y",null,Var("x"))));
let code4 = LetB("snd",Lam("x",null,Lam("y",null,Var("y"))));
let code3 = LetB("id",Lam("x",null,Var("x")),App(Var("id"),Lit("int",10)));
let code5 = LetB("compose",Lam("f",null,Lam("g",null,Lam("x",null,App(Var("f"),App(Var("g"),Var("x")))))));
// let code4 = LetB("id2",Lam("x",null,Var("x")));

// console.log(tc1.valid(code));
tc1.valid(code3);
tc1.valid(code2);
tc1.valid(code4);
tc1.valid(code5);
console.log(tc1.getTypeEnv().join("\n"));

// console.log(tc1.valid(Lam("x",null,App(Var("x"),Var("x")))));
// console.log(tc1.valid(App(Lit("bool",true),Lit("int",-1))));
// console.log(tc1.valid(code4));


// console.log("Type Env")

// console.log(tc1.valid(App(Var("id"),App(Var("id2"),Lit("int",10)))));

module.exports = TypeChecker;

// let code = App(
//     Lam("x",null,
//         Condition(
//             Lit("bool",true),
//             Var("x"),
//             Lit("int",0)
//         )
//     ),
//     Lit("int",10)
// );

// let code2 = Lam("x",null,
// Condition(
//     Lit("bool",true),
//     Var("x"),
//     Lit("int",0)
// ));
// let code3 = Lam("x",null,
// Condition(
//     Var("x"),
//     Lit("int",10),
//     Lit("int",0)
// ));