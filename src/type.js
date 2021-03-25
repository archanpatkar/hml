// Type checker
const saman = require("saman");
const { equal, merge } = require("saman");
const { sum, tagged } = require("styp");

const Type = sum("Types", {
    TVar:["v"],
    TCon:["name"],
    // TPair:["cons","cdr"],
    TArr:["t1","t2"]
});

// const Scheme = tagged("Scheme",["quantifiers","type"])

// const Scheme = sum("Scheme", {
//     Mono: ["t"],
//     Poly:["var","t"]
// });

// const Constraint = tagged("ConstraintEq",["left","right"]);

// const TypeEnv = () => new Map();

const TInt = Type.TCon("int");
const TBool = Type.TCon("bool");

const ops = ["ADD", "SUB", "DIV", "MUL"]
// const printType = (type) => Array.isArray(type) ? `(${printType(type[0])}->${printType(type[1])})` : type;

// Errors
const genericError = (msg) => { throw new Error(msg) };
const notInScope = (name) => genericError(`Variable --> '${name}' not in Scope`);
const defInScope = (name) => genericError(`Cannot redefine Variable --> '${name}'`);
const notType = (type,msg) => genericError(`Expected type '${printType(type)}' ${msg}`);
const typeMismatch = (type1,type2) => genericError(`Couldn't match the expected type: ${printType(type1)} with type: ${printType(type2)}`);
const nonFunction = (type) => genericError(`Tried to apply to non-Function type --> ${type}`);

// temp
const Lam = (param, type, body) => ({ node: "lambda", param: param, type: type, body: body });
const Pair = (fst,snd) => ({ node:"pair", fst:fst, snd:snd });
const Lit = (type, val) => ({ node: "literal", type: type, val: val });
const Var = (name) => ({ node: "var", name: name });
const LetB = (name,exp) => ({ node: "let", name: name, exp:exp });
const App = (lam, param) => ({ node: "apply", exp1: lam, exp2: param });
const Condition = (cond,e1,e2) => ({ node: "condition", cond:cond, exp1: e1, exp2: e2 });
const BinOp = (op, l, r) => ({ node: op, l: l, r: r });
const UnOp = (op,v) => ({ node: op, val: v });

class TypeEnv {
    constructor(parent) {
        this.env = {};
        this.parent = parent;
    }

    exists(name) {
        if (this.env[name]) return this.env[name];
        else if(this.parent) return this.parent.lookUp(name);
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
        else if(this.parent) return this.parent.lookUp(name);
        notInScope(name);
    }
}

class TypeChecker {
    constructor() {
        this.sym = new TypeEnv(null);
        this.count = 0;
        this.subst = {};
        // this.constraints = [];
        // this.variables = [];
        // this.ctable = new Map();
    }

    fresh() {
        let temp = "t" + this.count++;
        this.variables.push(temp);
        return Type.TVar(temp);
    }

    // addConstraint(type1,type2) {
    //     this.ctable.set(type1,type2);
    //     this.constraints.push(Constraint(type1,type2));
    // }

    occursCheck(v,t,subst) {
        if(saman.equal(v,t)) return true;
        else if(Type.TVar.is(t) && t.v in subst) 
            return occursCheck(v,subst[t.v],subst);
        else if(Type.TArr.is(t))
            return occursCheck(v,t.t2,subst) || occursCheck(v,t.t1,subst);
        return false;
    }

    unifyVar(v,t,subst) {
        if(v.v in subst) return unify(subst[v.v],t,subst);
        if(Type.TVar.is(t) && t.v in subst) return unify(v,subst[t.v],subst);
        if(occursCheck(v,t,subst)) return null;
        else {
            subst[v.v] = t;
            return subst;
        }
    }

    unify(t1,t2,subst={}) {
        if(equal(t1,t2)) return subst;
        else if(Type.TVar.is(t1)) return unifyVar(t1,t2,subst);
        else if(Type.TVar.is(t2)) return unifyVar(t2,t1,subst);
        else if(Type.TArr.is(t1) && Type.TArr.is(t2)) {
            subst = unify(t1.t2,t2.t2,subst);
            return unify(t1.t1,t2.t1,subst);
        }
        return null;
    }    

    apply(typ,subst) {
        if(!subst) return null;
        else if(Object.keys(subst).length == 0) return typ;
        else if(saman.equal(typ,TInt) || saman.equal(typ,TBool)) return typ;
        else if(Type.TVar.is(typ)) {
            if(typ.v in subst) return apply(subst[typ.v],subst);
            return typ;
        }
        else if(Type.TArr.is(typ)) {
            return Type.TArr(
                apply(typ.t1,subst),
                apply(typ.t2,subst)
            );
        }
        return null;
    }

    instantiate(type) {
        // let t1,t2;
        // if(Type.TVar.is(type.t1)) t1 = this.fresh();
        // if(Type.TArr.is(type.t2)) t2 = this.instantiate(type.t2);
        // else if(Type.TVar.is(type.t2)) t2 = this.fresh();
        // else t2 = type.t2;
        // return Type.TArr(t1,t2);
    }

    generalize(type) {
        
    }

    infer(ast,sym=this.sym) {
        if (ast.node == "literal") 
            return ast.type == "int"? TInt:TBool;
        else if (ast.node == "var") {
            const t = sym.lookUp(ast.name);
            // if(Type.TArr.is(t)) return this.instantiate(t);
            return t;
        }
        else if (ast.node == "let") {
            if(sym.exists(ast.name)) defInScope(ast.name);
            
            return null;
        }
        else if (ast.node == "condition") {
            const cond = this.infer(ast.cond,sym);
            const t1 = this.infer(ast.exp1,sym);
            const t2 = this.infer(ast.exp2,sym);
            const u1 = this.unify(cond,TBool);
            const u2 = this.unify(t1,t2);
            this.subst = merge(u1,u2);
            return this.apply(t1,this.subst);
        }
        else if (ast.node == "lambda") {
            const ne = new TypeEnv(sym);
            const tv = this.fresh();
            ne.addBinding(ast.param, tv);
            const body = this.infer(ast.body,ne);
            return Type.TArr(tv,body);
        }
        else if (ast.node == "apply") {
            const t1 = this.infer(ast.exp1,sym);
            const t2 = this.infer(ast.exp2,sym);
            const tv = this.fresh();
            this.unify(t1,Type.TArr(t2,tv));
            return tv;
        }
        return;
    }

    prove(ast) {
        // printType()
        return this.infer(ast).toString();
    }
}



const tc1 = new TypeChecker();
let code = App(
    Lam("x",null,
        Condition(
            Lit("bool",true),
            Var("x"),
            Lit("int",0)
        )
    ),
    Lit("int",10)
);

console.log(
    tc1.prove(
        Condition(
            Lit("bool",true),
            Lit("int",0),
            Lit("int",10)
        )
    )
);


module.exports = TypeChecker;