sig Hash {}
abstract sig Object {
	hash : one Hash
}

sig Blob extends Object {}

sig Name {}
sig Tree extends Object {
	objects : Hash -> Name
}

sig Commit extends Object {
	tree : one Hash,
	parent : set Hash
}

pred Invs {
  
  	// uma hash é única, cada objeto tem apenas uma hash e uma hash corresponde a um único objeto
  	all h: Hash | lone hash.h
  
  	// duas trees que tenham os mesmos objetos são a mesma tree
  	all t1,t2: Tree | t1.objects = t2.objects iff t1=t2
  
  	// trees só podem ter objetos do tipo tree ou blob
  	all t: Tree | t.objects.Name in Blob.hash+Tree.hash

  	// uma tree não pode ter dois objetos diferentes com o mesmo nome
  	all t: Tree, n: Name | lone t.objects.n
  	
	// uma tree não pode ter um objeto que seja ela própria
  	all t: Tree | t not in t.^(objects.Name.~hash)
  
  	// se dois commits tem as mesmas trees e os mesmos parents, então são o mesmo commit
  	all c1,c2: Commit | (c1.tree = c2.tree and c1.parent = c2.parent) iff c1=c2
  
  	// uma hash na relação tree do objeto commit é uma hash de um objeto tree
  	all c: Commit | c.tree in Tree.hash
  
  	// um parent de commit só pode ser um commit
  	all c: Commit | c.parent in Commit.hash
  	
  	// um commit não pode ter um parent que seja ele próprio
  	all c: Commit | c not in c.^(parent.~hash)
  
}
