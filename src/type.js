// Type checker
// Based on http://dev.stephendiehl.com/fun/006_hindley_milner.html
const { sum } = require("styp");
const { equal, merge } = require("saman");

const Type = sum("Types", {
    TVar: ["v"],
    TCon: ["name"],
    TPair: ["p1", "p2"],
    TArr: ["t1", "t2"]
});

const Scheme = sum("Scheme", {
    Forall: ["var", "type"]
});

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
    Cond: ["cond", "e1", "e2"]
});

// const Constraint = tagged("ConstraintEq",["left","right"]);

// const TypeEnv = () => new Map();

const TInt = Type.TCon("int");
const TBool = Type.TCon("bool");

const ops = ["ADD", "SUB", "DIV", "MUL", "AND", "OR", "NOT"];
function printType(type) {
    if(Type.TCon.is(type)) return type.name;
    if(Type.TVar.is(type)) return type.v;
    if(Type.TArr.is(type)) return `${printType(type.t1)} -> ${printType(type.t2)} `
    if(Scheme.Forall.is(type)) 
        return type.var.length?`forall ${type.var.join(" ")}. ${printType(type.type)}`:printType(type.type);
}

// Errors
const genericError = (msg) => { throw new Error(msg) };
const notInScope = (name) => genericError(`Variable --> '${name}' not in Scope`);
const defInScope = (name) => genericError(`Cannot redefine Variable --> '${name}'`);
const notUnifiable = (type1, type2, msg = "") => genericError(`Cannot unify types: '${type1.toString()}' with '${type2.toString()}' ${msg}`);
const failedOccursCheck = (name) => genericError(`Failed Occurs Check --> '${name.toString()}'`);
// const notType = (type,msg) => genericError(`Expected type '${printType(type)}' ${msg}`);
// const typeMismatch = (type1,type2) => genericError(`Couldn't match the expected type: ${printType(type1)} with type: ${printType(type2)}`);
// const nonFunction = (type) => genericError(`Tried to apply to non-Function type --> ${type}`);

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
        console.log("here3!");
        console.log(name);
        console.log(this.env)
        if (this.env[name]) return this.env[name];
        if (this.parent) return this.parent.lookUp(name);
        notInScope(name);
    }
}

class TypeChecker {
    constructor() {
        this.env = new TypeEnv(null);
        this.count = 0;
        this.subst = {};
        // this.constraints = [];
    }

    fresh() {
        let temp = "t" + this.count++;
        return Type.TVar(temp);
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
        if (this.occursCheck(v, t, subst)) failedOccursCheck(v);
        else {
            subst[v.v] = t;
            return subst;
        }
    }

    unify(t1, t2, subst = {}) {
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
        if (Type.TVar.is(typ)) {
            if (typ.v in subst) return this.apply(subst[typ.v], subst);
            return typ;
        }
        if (Type.TArr.is(typ)) {
            return Type.TArr(
                this.apply(typ.t1, subst),
                this.apply(typ.t2, subst)
            );
        }
        if (Scheme.Forall.is(typ)) {
            typ.var.forEach(v => delete subst[v.v]);
            return Scheme.Forall(type.var, this.apply(typ.type, subst));
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
        console.log("here!");
        console.log(type)
        if (Type.TCon.is(type)) return new Set();
        if (Type.TVar.is(type)) return new Set([type.v]);
        if (Type.TArr.is(type)) return new Set([...this.ftv(type.t1), ...this.ftv(type.t2)]);
        if (Scheme.Forall.is(type)) {
            const bounded = new Set(type.var.map(v => v.v));
            return new Set([...this.ftv(type.type)].filter(v => !bounded.has(v)));
        }
        return null;
    }

    instantiate(type) {
        console.log("here2!");
        const ns = {}
        type.var.map(v => ns[v.name] = this.fresh());
        return this.apply(type.type, ns);
    }

    generalize(type, env) {
        const enftv = new Set(Object.values(env.env).map(t => this.ftv(t).entries()).flat());
        console.log(printType(type));
        const as = new Set([...(this.ftv(type))].filter(v => !enftv.has(v)));
        return Scheme.Forall([...as.entries()].map(v => Type.TVar(v)), type);
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
            const u1 = this.unify(cond, TBool);
            const u2 = this.unify(t1, t2);
            this.subst = merge(this.subst, merge(u1, u2));
            return this.apply(t1);
        }
        else if (ast.node == "lambda") {
            const tv = this.fresh();
            const ne = new TypeEnv(env);
            ne.addBinding(ast.param, Scheme.Forall([],tv));
            console.log(ne);
            const body = this.infer(ast.body, ne);
            console.log(ne)
            return this.apply(Type.TArr(tv, body));
        }
        else if (ast.node == "apply") {
            const tv = this.fresh();
            const t1 = this.infer(ast.exp1, env);
            const t2 = this.infer(ast.exp2, this.applyEnv(env));
            this.subst = merge(this.subst, this.unify(this.apply(t1), Type.TArr(t2, tv)));
            return this.apply(tv);
        }
        return;
    }

    prove(ast) {
        return printType(this.infer(ast));
    }
}



const tc1 = new TypeChecker();
let code = Lam("x", null, Var("x"));
let code2 = Lam("x",null,Lam("y",null,Var("x")));
let code3 = LetB("id",Lam("x",null,Var("x")),App(Var("id"),Lit("int",10)));
let code4 = LetB("id",Lam("x",null,Var("x")));


console.log(tc1.prove(code4));


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