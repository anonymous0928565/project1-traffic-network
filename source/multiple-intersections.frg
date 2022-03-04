#lang forge/bsl

/* 
Stretch Goal:
model an entire traffic network. have cars start at various locations, and have them 
each try to get to their destinations. along the way, they will encounter intersections
which may slow their progress. the goal of the model is to find the optimal way to synch
intersection lights such that every car gets to its destination in minimum time.

Solvable Challenges:
- How do cars know which roads to take to get to their destination?
- How do we represent the passing of time with our turn-based model of state? 
  (start wt bridge crossing)
- How do we prevent cars from passing through each other?
- How do we model connections between intersections (roads)?
- Should roads have multiple lanes? (definitely start with single-lane)

Potentially Out-of-Scope Challenges:
- A useful traffic model should settle on a scheme that works well on average. The model described 
  above would instead solve for whatever specific routes are generated in a given instance, which 
  may be useless when generalized (think overfitting).
- No matter what, our model will not be able to capture the precise timing of real-world roads.
- Our model simplifies a road network to a strict grid.
- For now, we are forcing all streets to intersect all avenues.

Ethics:
- The model treats automobiles as the sole and rightful users of roads (the only stakeholders). 
  We do not consider pedestrians in the model, and we assume each car is an ideal actor. This
  perpetuates the supremacy of car culture over transportation, a culture that comes with
  countless problems. Cars are low capacity, energy inefficient, more prone to traffic jams,
  and dangerous in urban areas. Also, car culture informs the way that cities are built, leading
  to excessively sparse, atomized neighborhoods, dangerous street-road hybrids, and enourmous
  amounts of parking space. This makes it more difficult to develop a sense of community, and
  isolates people from the space around them.
*/

abstract sig Direction {}
one sig North extends Direction {}
one sig South extends Direction {}
one sig East extends Direction {}
one sig West extends Direction {}

abstract sig LightStatus {}
one sig Red extends LightStatus {}
one sig Yield extends LightStatus {}
// For lefts, green represents the flashing green arrow (protected turn)
one sig Green extends LightStatus {}

abstract sig Road {}
// streets run north-south
sig Street extends Road {
    westStr: lone Street,
    eastStr: lone Street,
    intersection: func Avenue -> Intersection // all streets intersect with all avenues
}
// avenues run east-west
sig Avenue extends Road {
    northAve: lone Avenue,
    southAve: lone Avenue
}

sig Intersection {
    st: one Street,
    av: one Avenue,
    color: func State -> Direction -> LightStatus, // represents the main color of the light
    lcolor: func State -> Direction -> LightStatus // represents the color of the left turn light
}

sig State {
    next: lone State
}

pred ValidStates {
    all s: State {
        all i: Intersection, d: Direction | {
            i.color[s, d] != Yield

            // roads and intersections correspond
            i = i.st.intersection[i.av]
        }
    }

    all str: Street | {
        not reachable[str, str, eastStr]
        not reachable[str, str, westStr]
        one str.eastStr => str.eastStr.westStr = str
        one str.westStr => str.westStr.eastStr = str
    }

    all ave: Avenue | {
        not reachable[ave, ave, northAve]
        not reachable[ave, ave, southAve]
        one ave.northAve => ave.northAve.southAve = ave
        one ave.southAve => ave.southAve.northAve = ave
    }
}

pred SafeLights {
    all s: State, i: Intersection | {
        // At least one road in intersection must have all red lights both ways
        (i.color[s, North] = Red and i.color[s, South] = Red and
        i.lcolor[s, North] = Red and i.lcolor[s, South] = Red) or
        (i.color[s, East] = Red and i.color[s, West] = Red and
        i.lcolor[s, East] = Red and i.lcolor[s, West] = Red)

        // If a light is on, the left-turn light on the opposite side must be yield or red
        i.color[s, North] = Green => i.lcolor[s, South] != Green
        i.color[s, South] = Green => i.lcolor[s, North] != Green
        i.color[s, East] = Green => i.lcolor[s, West] != Green
        i.color[s, West] = Green => i.lcolor[s, East] != Green
    }
}

// This may become unnecessary when we constrain minimum-time solution to traffic
pred NoFullStop {
    all s: State, i: Intersection | {
        some d: Direction | {
            i.color[s, d] != Red or i.lcolor[s, d] != Red
        }
    }
}

pred CanTransition[pre: State, post: State] {
    some i: Intersection, d: Direction | {
        i.color[pre, d] != i.color[post, d] or i.lcolor[pre, d] != i.lcolor[post, d]
    }

    // Green Wave
    all str: Street, ave: Avenue | {
        all disj i1, i2: Intersection | {
            (i1 = str.intersection[ave] and i2 = str.intersection[ave.northAve] and
            i1.color[pre, North] = Green and i1.color[post, North] = Red) =>
            i2.color[post, North] = Green

            (i1 = str.intersection[ave] and i2 = str.intersection[ave.southAve] and
            i1.color[pre, South] = Green and i1.color[post, South] = Red) =>
            i2.color[post, South] = Green

            (i1 = str.intersection[ave] and i2 = str.eastStr.intersection[ave] and
            i1.color[pre, East] = Green and i1.color[post, East] = Red) =>
            i2.color[post, East] = Green

            (i1 = str.intersection[ave] and i2 = str.westStr.intersection[ave] and
            i1.color[pre, West] = Green and i1.color[post, West] = Red) =>
            i2.color[post, West] = Green
        }
    }
}

// In future, start init with a traffic jam, and make final the state when all cars have crossed the intersection 
// (to make it interesting, restrict time to find optimal light pattern)
pred TransitionStates {
    some init, final: State | {
        reachable[final, init, next]
    }

    all s: State | {
        one s.next => CanTransition[s, s.next]
    }
}

run {
    ValidStates
    TransitionStates
    SafeLights
    NoFullStop
} for exactly 10 State, exactly 9 Intersection, exactly 6 Road, exactly 3 Street, exactly 3 Avenue
  for {next is linear}