open util/integer

sig Drone
{
    coordonnees : Coordonnees
}

sig Receptacle
{
    coordonnees : Coordonnees
}

sig Entrepot
{
    coordonnees : Coordonnees
}

sig Coordonnees
{
    x : Int,
    y : Int
}


// Fonctions
fun abs[x: Int]: Int {
    x >= 0 => x else x.mul[-1]
}

pred coordonneesEgales[c0,c1 : Coordonnees]
{
	c0.x = c1.x && c0.y = c1.y
}

/* Receptable.coordonnes != Entrepot.coordonnes */
fact invCoordonnees
{
	initInstances
	coordonneesUniques
	coordonneesReceptacles
	coordonneesEntrepot
	coordonneesDrones
}

// Initialisation du nombre d'instances qui sont contraintes
pred initInstances
{
	one Entrepot
	#Drone = 3 			// DNB
	#Receptacle = 2	// RNB
}

// Les instances de Coordonnées doivent correspondre à des cases différentes
pred coordonneesUniques
{
	no c0, c1 : Coordonnees | (c0 != c1 && c1.coordonneesEgales[c0])
}

// Les réceptacles ne peuvent avoir les mêmes coordonnées
pred coordonneesReceptacles
{
	no r0, r1 : Receptacle | (r0 != r1 && r0.coordonnees = r1.coordonnees)
}

// Les réceptacles ne peuvent pas avoir les mêmes coordonnées que les entrepôts
pred coordonneesEntrepot
{
	no r : Receptacle, e : Entrepot | r.coordonnees = e.coordonnees
}

// Les drones ne peuvent se trouver sur les mêmes cases
pred coordonneesDrones
{
	no d0, d1 : Drone | (d0 != d1  && d0.coordonnees = d1.coordonnees && (no e0 : Entrepot | d0.coordonnees = e0.coordonnees))
}

assert assertCoordonneesDrones 
{
	no d0 : Drone | 
			(no e0 : Entrepot | e0.coordonnees = d0.coordonnees) 
 	 &&	(some d1 : Drone | d0 != d1 && d0.coordonnees = d1.coordonnees)
}

check assertCoordonneesDrones for 10

// Prédicats sur les distances et localisations géographiques
pred positionVoisin[c0, c1 : Coordonnees]
{
	abs[c0.x.sub[c1.x]].add[abs[c0.y.sub[c1.y]]] =< 3
}

pred go
{
    
}

run go for 5
