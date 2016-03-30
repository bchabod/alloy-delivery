open util/integer

/********************************* Signatures *********************************/

/**
 * Signature de l'objet Drone
 * Attributs :
 *    coordonnees : coordonnees actuelles du drone
 */
sig Drone
{
    coordonnees : Coordonnees,
//	capaciteMax : Int, 
//	contenanceActuel : Int,
//	batterie : Int
}

/**
 * Signature de l'objet Receptacle
 * Attributs :
 *    coordonnees : coordonnees du receptables
 *    receptaclesVoisins : tous les receptables voisins de ce receptable
 */
sig Receptacle
{
    coordonnees : Coordonnees,
//	capaciteMax : Int, 
//	contenanceActuel : Int
	receptaclesVoisins : some Receptacle
}

/**
 * Signature de l'objet Entrepot
 * Attributs :
 *    coordonnees : coordonnees de l'entrepot
 *    receptaclesVoisins : tous les receptables voisins de cet entrepot
 */
sig Entrepot
{
    coordonnees : Coordonnees,
	receptaclesVoisins : some Receptacle
}

/**
 * Signature de l'objet Coordonnees
 * Attributs :
 *    x : coordonnee X (entier) de cette coordonnee
 *    Y : coordonnee Y (entier) de cette coordonnee
 */
sig Coordonnees
{
    x : Int,
    y : Int
}

/*
sig Commande
{
	contenanceActuel: Int
}
*/

/********************************* Fonctions *********************************/

/** 
  * Calcule la valeur absolue d'un entier
  * Retourne : la valeur absolue de l'entier X
  */
fun abs[x: Int]: Int {
    x >= 0 => x else x.mul[-1]
}

/********************************* Faits *********************************/

/** 
  * Ensemble des faits pour placer les elements avec leurs coordonnees
  */
fact invCoordonnees
{
	initInstances
	predCoordonnees
	predicatsPositions

	receptaclesVoisins
}

/*
fact initCapacites
{
	capacitesReceptacles
	capacitesDrones
	batterieDrones
}
*/

/********************************* Predicats *********************************/

/** 
  * Vérifie que deux coordonnees sont egales
  */
pred coordonneesEgales[c0,c1 : Coordonnees]
{
	c0.x = c1.x && c0.y = c1.y
}

/** 
  * Initialise le nombre d'instances des objets
  */
pred initInstances
{
	one Entrepot
	#Drone = 3 			// DNB
	#Receptacle = 5	// RNB
}

/** 
  * Ensemble des predicats qui contraignent les coordonnees
  */
pred predCoordonnees
{
	coordonneesUniques
	coordonneesReceptacles
	coordonneesEntrepot
	coordonneesDrones
}

/** 
  * Verifie que les instances de Coordonnees sont sur des cases differentes
  */
pred coordonneesUniques
{
	no c0, c1 : Coordonnees | (c0 != c1 && c1.coordonneesEgales[c0])
}

/** 
  * Verifie que les receptacles soient sur des coordonnees differentes
  */
pred coordonneesReceptacles
{
	no r0, r1 : Receptacle | (r0 != r1 && r0.coordonnees = r1.coordonnees)
}

/** 
  * Verifie que les receptacles ne soient pas sur les coordonnees des entrepots
  */
pred coordonneesEntrepot
{
	no r : Receptacle, e : Entrepot | r.coordonnees = e.coordonnees
}

/** 
  * Verifie que les drones ne soient pas sur les memes coordonnees
  */
pred coordonneesDrones
{
	no d0, d1 : Drone | (d0 != d1  && d0.coordonnees = d1.coordonnees && (no e0 : Entrepot | d0.coordonnees = e0.coordonnees))
}

/** 
  * Verifie que deux coordonnees soient au plus d'une distance de 3 cases (distance de manhattan)
  */
pred positionVoisin[c0, c1 : Coordonnees]
{
	abs[c0.x.sub[c1.x]].add[abs[c0.y.sub[c1.y]]] =< 3
}

/** 
  * Verifie que deux coordonnees soient au plus d'une distance de 3 cases (distance de manhattan)
  */
pred predicatsPositions
{
	positionVoisinEntrepot
	positionVoisinReceptacles
}

pred positionVoisinEntrepot
{
	all e0 : Entrepot | (some r0 : Receptacle | e0.coordonnees.positionVoisin[r0.coordonnees])
}

pred positionVoisinReceptacles
{
	all r0 : Receptacle | (some r1 : Receptacle | r0 != r1 && r0.coordonnees.positionVoisin[r1.coordonnees])
}

/*
pred capacitesReceptacles
{
	all r : Receptacle | r.capaciteMax = 7 && r.contenanceActuel = 0//RCAP
}

pred capacitesDrones
{
	all d : Drone | d.capaciteMax = 2 && d.contenanceActuel = 0 //DCAP
}

pred batterieDrones
{
	all d : Drone | d.batterie = 3
}
*/

pred receptaclesVoisins
{
	all e0 : Entrepot | #e0.receptaclesVoisins > 1
	all e0 : Entrepot, r0 : e0.receptaclesVoisins | e0.coordonnees.voisin[r0.coordonnees] 
	all r0 : Receptacle | !(r0 in r0.receptaclesVoisins)
	all r0 : Receptacle, r1 : r0.receptaclesVoisins | r0.coordonnees.voisin[r1.coordonnees] && r0 in r1.receptaclesVoisins
	//all r0, r1 : Receptacle | r1 in r0.*receptaclesVoisins
	all e0 : Entrepot, r0 : Receptacle | some r1 : e0.receptaclesVoisins | r0 in r1.*receptaclesVoisins
//all e0 : Entrepot, r0 : e0.receptaclesVoisins, r1 : Receptacle |  r1 in r0.*receptaclesVoisins
}

pred voisin[c0,c1 : Coordonnees]
{
	(c0.x = c1.x && c0.y = c1.y.add[1]) ||
	(c0.x = c1.x && c0.y = c1.y.sub[1]) ||
	(c0.x = c1.x.add[1] && c0.y = c1.y) ||
	(c0.x = c1.x.sub[1] && c0.y = c1.y)
}

pred chemin[c0,c1 : Coordonnees]
{
	
}

/********************************* Assertions *********************************/

assert assertCoordonneesDrones 
{
	no d0 : Drone | 
			(no e0 : Entrepot | e0.coordonnees = d0.coordonnees) 
 	 &&	(some d1 : Drone | d0 != d1 && d0.coordonnees = d1.coordonnees)
}

check assertCoordonneesDrones for 10 but 6 int

//

assert assertReceptablesVoisinsEntrepotMaisPasEntreEux 
{
	some r0, r1 : Receptacle, e0 : Entrepot
	 | r0 != r1 && 
	   !r0.coordonnees.voisin[r1.coordonnees] && 
	   e0.coordonnees.voisin[r0.coordonnees] &&
	   e0.coordonnees.voisin[r1.coordonnees]
}

check assertReceptablesVoisinsEntrepotMaisPasEntreEux for 8 but 6 int

/********************************* Lancements *********************************/

// Run Go
pred go
{
}

run go for 8 but 6 int
