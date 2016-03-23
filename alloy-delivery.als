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

pred coordonneesEgales[c0,c1 : Coordonnees]
{
	c0.x = c1.x && c0.y = c1.y
}

/* Receptable.coordonnes != Entrepot.coordonnes */
fact invCoordonnees
{
	coordonneesUniques
	coordonneesReceptacles
	coordonneesEntrepot
}

// Les instances de Coordonnées doivent correspondre à des cases différentes
pred coordonneesUniques
{
	no c0, c1 : Coordonnees | (c0 != c1 && c0.x = c1.x && c0.y = c1.y)
}

assert assertCoordonnees
{
   coordonneesUniques => (all c0 : Coordonnees | some c1 : Coordonnees | c1.coordonneesEgales[c0])
}

check assertCoordonnees for 20

// Les réceptacles ne peuvent avoir les mêmes coordonnées
pred coordonneesReceptacles
{
	no r0, r1 : Receptacle | (r0 != r1 && r0.coordonnees.coordonneesEgales[r1.coordonnees])
}

assert assertCoordonneesReceptacles
{
	coordonneesReceptacles => (all r0 : Receptacle | some r1 : Receptacle | r0.coordonnees.coordonneesEgales[r1.coordonnees])
}

check assertCoordonneesReceptacles for 20

// Les réceptacles ne peuvent pas avoir les mêmes coordonnées que les entrepôts
pred coordonneesEntrepot
{
	no r : Receptacle, e : Entrepot | r.coordonnees.coordonneesEgales[e.coordonnees]
}

assert assertCoordonneesEntrepot
{
	coordonneesEntrepot => (all r0 : Receptacle | some e0 : Entrepot | r0.coordonnees.coordonneesEgales[e0.coordonnees])
}

check assertCoordonneesEntrepot for 3


pred go
{
    one Entrepot
}

run go for 3
