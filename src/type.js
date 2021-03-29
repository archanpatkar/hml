// Type checker
// Based on http://dev.stephendiehl.com/fun/006_hindley_milner.html
const { sum } = require("styp");
const { equal } = require("saman");
const { Expr } = require("./ast");

const uops = ["NEG", "NOT"];
const bops = ["ADD", "SUB", "DIV", "MUL", "AND", "OR", "GT", "LT", "EQ"];

// Type Defs
const Type = sum("Types", {
    TVar: ["v"],
    TCon: ["name"],
    TArr: ["t1", "t2"]
});

const Scheme = sum("Scheme", {
    Forall: ["var", "type"]
});

const TInt = Type.TCon("int");
const TBool = Type.TCon("bool");
const TUnit = Type.TCon("unit");

const PrimTypes = {
    "int":TInt,
    "bool":TBool,
    "unit":TUnit
};

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

// const Constraint = tagged("ConstraintEq",["left","right"]);

// Errors
const genericError = (msg) => { throw new Error(msg) };
const notInScope = (name) => genericError(`Variable: '${name}' not in Scope`);
const defInScope = (name) => genericError(`Cannot redefine Variable: '${name}'`);
const notUnifiable = (type1, type2, msg = "") => genericError(`Cannot unify types: ${printType(type1)} with ${printType(type2)} ${msg}`);
const failedOccursCheck = (v,name) => genericError(`Cannot construct infinite type: ${printType(v)} = ${printType(name)}`);

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
        const enftv = this.ftvEnv(env);
        const as = new Set([...(this.ftv(type))].filter(v => !enftv.has(v)));
        return Scheme.Forall([...as].map(v => Type.TVar(v)), type);
    }

    inferLet(ast,env) {
        if (env.exists(ast.name)) defInScope(ast.name);
        const t1 = this.infer(ast.e1,env);
        const tdash = this.generalize(t1,this.applyEnv(env,this.subst));
        if(ast.e2) {
            const ne = new TypeEnv(env);
            ne.addBinding(ast.name, tdash);
            return this.infer(ast.e2,ne);
        }
        env.addBinding(ast.name,tdash);
        return tdash;
    }

    inferLetRec(ast,env) {

    }

    inferCond(ast,env) {
        const cond = this.infer(ast.cond, env);
        const t1 = this.infer(ast.e1, env);
        const t2 = this.infer(ast.e2, env);
        this.unify(cond, TBool);
        this.unify(t1, t2);
        return this.apply(t1);
    }

    inferLam(ast,env) {
        const tv = this.fresh();
        const ne = new TypeEnv(env);
        ne.addBinding(ast.param, Scheme.Forall([],tv));
        const body = this.infer(ast.body, ne);
        return this.apply(Type.TArr(tv, body));
    }

    inferApp(ast,env) {
        const t1 = this.infer(ast.e1, env);
        const t2 = this.infer(ast.e2, this.applyEnv(env));
        const tv = this.fresh();
        this.unify(this.apply(t1), Type.TArr(t2, tv));
        return this.apply(tv);
    }

    inferFix(ast,env) {
        const t = this.infer(ast.e,env);
        const tv = this.fresh();
        this.unify(Type.TArr(tv,tv),t);
        return this.apply(tv);
    }  

    inferUnOp(ast,env) {
        const t = this.infer(ast.v,env);
        const tv = this.fresh();
        this.unify(Type.TArr(t,tv),optypes[ast.op]);
        return this.apply(tv);
    }
    
    inferBinOp(ast,env) {
        const t1 = this.infer(ast.l,env);
        const t2 = this.infer(ast.r,env);
        const tv = this.fresh();
        let op = optypes[ast.op];
        if(Scheme.Forall.is(op)) op = this.instantiate(op);
        this.unify(Type.TArr(t1,Type.TArr(t2,tv)),op);
        return this.apply(tv);
    }

    inferPair(ast,env) {
        const fst = this.infer(ast.fst,env);
        const snd = this.infer(ast.snd,env);
        const tv = this.fresh();
        return Type.TArr(Type.TArr(fst,Type.TArr(snd,tv)),tv);
    }

    infer(ast, env = this.env) {
        if (Expr.Lit.is(ast)) return PrimTypes[ast.type];
        if (Expr.Var.is(ast)) return this.lookUp(ast.name,env);
        if (Expr.Let.is(ast)) return this.inferLet(ast,env);
        if (Expr.Cond.is(ast)) return this.inferCond(ast,env);
        if (Expr.Lam.is(ast)) return this.inferLam(ast,env);
        if (Expr.App.is(ast)) return this.inferApp(ast,env);
        if (Expr.Fix.is(ast)) return this.inferFix(ast,env);
        if (Expr.Pair.is(ast)) return this.inferPair(ast,env);
        if (Expr.UnOp.is(ast)) return this.inferUnOp(ast,env);
        if (Expr.BinOp.is(ast)) return this.inferBinOp(ast,env);
        genericError("Unrecognized AST Node");
    }

    getType(name) {
        const t = this.env.lookUp(name);
        if(Scheme.Forall.is(t)) {
            let i = 0;
            const ns = {}
            let as;
            if(t.var[0] && t.var[0].v == "a") as = t.var;
            else as = t.var.map(v => ns[v.v] = Type.TVar(String.fromCharCode((i++)+97)));
            return printType(Scheme.Forall(as, this.apply(t.type, ns)));
        }
        return printType(t);
    }

    getTypeEnv() {
        return Object.keys(this.env.env).map(k => `${k} :: ${this.getType(k)}`)
    }

    valid(ast) {
        this.subst = {};
        return printType(this.infer(ast));
    }
}



// const tc1 = new TypeChecker();
// let code = Lam("x", null, Var("x"));
// let code2 = LetB("fst",Lam("x",null,Lam("y",null,Var("x"))));
// let code4 = LetB("snd",Lam("x",null,Lam("y",null,Var("y"))));
// let code3 = LetB("id",Lam("x",null,Var("x")),App(Var("id"),Lit("int",10)));
// let code5 = LetB("compose",Lam("f",null,Lam("g",null,Lam("x",null,App(Var("f"),App(Var("g"),Var("x")))))));

// App(Lam("x",null,Lam("y",null,Var("x"))),)
// LetB("p4",);
// let code6 = LetB("p1",Pair(Lit("int",10),Lit("bool",false)));
// let code7 = App(Var("p1"),Var("fst"));
// let code8 = App(Var("p1"),Var("snd"));
// let code4 = LetB("id2",Lam("x",null,Var("x")));

// tc1.valid(code2);
// tc1.valid(code4);
// tc1.valid(code6);
// console.log(tc1.valid(code7));
// console.log(tc1.valid(code8));
// console.log(tc1.getTypeEnv().join("\n"));

// console.log(tc1.valid(code));
// tc1.valid(code3);
// tc1.valid(code2);
// tc1.valid(code4);
// tc1.valid(code5);
// console.log(tc1.getTypeEnv().join("\n"));

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