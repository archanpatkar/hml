const id = `let id x = x`;
const compose = `let compose f g x = f (g x)`;
const kestral = `let kestral x y = x`;
const kite = `let kite x y = y`;
const fst = `let fst p = p kestral`;
const snd = `let snd p = p kite`;

module.exports = [id,compose,kestral,kite,fst,snd];