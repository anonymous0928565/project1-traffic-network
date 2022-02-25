#lang forge/bsl

abstract sig Color {}
one sig Red extends Color {}
one sig Yellow extends Color {}
one sig Green extends Color {}

sig Light {}

one sig Intersection {
    ud: one Light,
    lr: one Light
}

sig State {
    next: lone State,
    lcolor: func Light -> Color
}

pred SafeLights {
    all s: State, i: Intersection | {
        (s.lcolor[i.ud] = Green or
        s.lcolor[i.ud] = Yellow) =>
        s.lcolor[i.lr] = Red

        (s.lcolor[i.lr] = Green or
        s.lcolor[i.lr] = Yellow) =>
        s.lcolor[i.ud] = Red
    }
}

pred NoFullStop {
    all s: State, i: Intersection | {
        some l: Light | {
            i.ud = l or i.lr = l
            s.lcolor[l] != Red
        }
    }
}

pred CanTransition[pre: State, post: State] {
    some l: Light | {
        pre.lcolor[l] != post.lcolor[l]
    }
    
    all l: Light | pre.lcolor[l] != post.lcolor[l] implies {
        pre.lcolor[l] = Green =>
        post.lcolor[l] = Yellow

        pre.lcolor[l] = Yellow =>
        post.lcolor[l] = Red

        pre.lcolor[l] = Red =>
        post.lcolor[l] = Green
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