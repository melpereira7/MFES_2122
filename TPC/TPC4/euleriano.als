//Mostre como pode usar o Alloy para encontrar um circuito Euleriano num grafo não-orientado e ligado (sem lacetes). Mais informações aqui:
//https://en.wikipedia.org/wiki/Eulerian_path
//Defina também um comando run que exemplifica com um grafo completo com 5 nodos.
//Desenvolva o modelo no Alloy Analyzer e copie o modelo final para a caixa de resposta, tendo o cuidado de usar uma fonte monospaced (Arial Mono) que preserve a formatação.


sig Node {
 	var edge: set Node,
	var path: set Node
}

var sig Elected in Node {}

one sig First in Node {}


// Especifique as condições iniciais do sistema

fact Init {
	some Node
	no edge&iden //grafo sem lacete: nodos não ligam a eles próprios
	all n1: Node, n2: n1.edge | n1 in n2.edge //grafo não-orientado: se edge tem n1->n2, então também tem n2->n1
	all n: Node | some n.^(edge) //grafo ligado
	no path
	Elected = First
}

pred next[n1: Elected, n2: Node] {
	//guards
	
	n2 in n1.edge	

	//effects

	Elected' = Elected - n1 + n2
	path' = path + n1->n2
	edge' = edge - n1->n2 - n2->n1
	
	//frame conditions
	Node' = Node
	First' = First
}

pred nop {
	//guards
	no edge and Elected = First
	
	// frame conditions
	Node' = Node
	Elected' = Elected
	First' = First
	edge' = edge
	path' = path
}

fact Traces {
	always (
		nop or 
		some n1: Elected, n2: Node | next[n1,n2]
	)
}


run {
	all n: Node | n.edge = Node-n
} for exactly 5 Node, 20 steps
