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

Potentially Unsolvable Challenges:
- A useful traffic model should settle on a scheme that works well on average. The model described 
  above would instead solve for whatever specific routes are generated in a given instance, which 
  may be useless when generalized (think overfitting).
- No matter what, our model will not be able to capture the precise timing of real-world roads.

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

abstract sig LightStatus {}

one sig Red extends LightStatus {}
/* Getting Rid of Yellow Light
i think we should take out yellow because it doesn't actually do anything interesting.
we can just assume that for some short time before a green->red transition, the light
turns yellow. also, getting rid of yellow makes modeling time a lot easier to think about 
(and easier to program of course).
*/
one sig Yellow extends LightStatus {}
one sig Green extends LightStatus {}

sig Light {}

one sig Intersection {
    north: one Light,
    south: one Light,
    east: one Light,
    west: one Light
}

sig State {
    next: lone State,
    // color represents the main color of the light
    color: func Light -> LightStatus,
    // lcolor represents the color of the left turn light
    lcolor: func Light -> LightStatus
}

pred SafeLights {
    all s: State, i: Intersection | {
        (s.color[i.north] = Green or s.color[i.north] = Yellow or
         s.color[i.south] = Green or s.color[i.south] = Yellow) =>
        (s.color[i.east] = Red and s.color[i.west] = Red)

        (s.color[i.east] = Green or s.color[i.east] = Yellow or
         s.color[i.west] = Green or s.color[i.west] = Yellow) =>
        (s.color[i.north] = Red and s.color[i.south] = Red)
    }
}

pred NoFullStop {
    all s: State, i: Intersection | {
        some l: Light | {
            i.ud = l or i.lr = l
            s.color[l] != Red
        }
    }
}

pred CanTransition[pre: State, post: State] {
    some l: Light | {
        pre.color[l] != post.color[l]
    }
    
    all l: Light | pre.color[l] != post.color[l] implies {
        pre.color[l] = Green =>
        post.color[l] = Yellow

        pre.color[l] = Yellow =>
        post.color[l] = Red

        pre.color[l] = Red =>
        post.color[l] = Green
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
    TransitionStates
    SafeLights
    NoFullStop
} for exactly 5 State, exactly 1 Intersection, exactly 2 Light
  for {next is linear}