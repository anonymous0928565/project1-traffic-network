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
/* Getting Rid of Yellow Light
i think we should take out yellow because it doesn't actually do anything interesting.
we can just assume that for some short time before a green->red transition, the light
turns yellow. also, getting rid of yellow makes modeling time a lot easier to think about 
(and easier to program of course).
*/
// For now, yellow will represent the solid green "yield" status of a left turn lane
one sig Yellow extends LightStatus {}
// For lefts, green represents the flashing green arrow (protected turn)
one sig Green extends LightStatus {}

abstract sig Road {}
// streets run north-south
sig Street extends Road {
    nextStr: lone Street,
    intersection: func Avenue -> Light // all streets intersect with all avenues
}
// avenues run east-west
sig Avenue extends Road {
    nextAve: lone Avenue
}

sig Light {
    st: one Street,
    av: one Avenue,
    color: func State -> Direction -> LightStatus, // represents the main color of the light
    lcolor: func State -> Direction -> LightStatus // represents the color of the left turn light
}

// TODO: integrate cars (and time) into the model
sig Car {}

sig State {
    next: lone State
}

pred ValidStates {
    all s: State {
        all l: Light, d: Direction | {
            // for now, our implementation does not allow main lights to be yellow (only lefts)
            l.color[s, d] != Yellow

            // lights and intersections correspond
            l = l.st.intersection[l.av]
        }

        // nextStr is linear
        all str: Street | {
            not reachable[str, str, nextStr]
        }

        // nextAve is linear
        all ave: Avenue | {
            not reachable[ave, ave, nextAve]
        }
    }
}

pred SafeLights {
    all s: State, l: Light | {
        // At least one road in intersection must have all red lights both ways
        (l.color[s, North] = Red and l.color[s, South] = Red and
        l.lcolor[s, North] = Red and l.lcolor[s, South] = Red) or
        (l.color[s, East] = Red and l.color[s, West] = Red and
        l.lcolor[s, East] = Red and l.lcolor[s, West] = Red)

        // If a light is on, the left-turn light on the opposite side must be yield or red
        l.color[s, North] = Green => l.lcolor[s, South] != Green
        l.color[s, South] = Green => l.lcolor[s, North] != Green
        l.color[s, East] = Green => l.lcolor[s, West] != Green
        l.color[s, West] = Green => l.lcolor[s, East] != Green
    }
}

// This may become unnecessary when we constrain minimum-time solution to traffic
pred NoFullStop {
    all s: State, l: Light | {
        some d: Direction | {
            l.color[s, d] != Green or l.lcolor[s, d] != Green
        }
    }
}

pred CanTransition[pre: State, post: State] {
    some l: Light, d: Direction | {
        l.color[pre, d] != l.color[post, d] or l.lcolor[pre, d] != l.lcolor[post, d]
    }
    
    // TODO: implement further transition rules
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
} for exactly 5 State, exactly 1 Light, exactly 2 Road
  for {next is linear}