sig User {
	follows : set User,
	sees : set Photo,
	posts : set Photo,
	suggested : set User
}

sig Influencer extends User {}

sig Photo {
	date : one Day
}
sig Ad extends Photo {}

sig Day {}

// Specify the following properties
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true

pred inv1 {
	// Every image is posted be one user
	all p: Photo | one u: User | u->p in posts 
}


pred inv2 {
	// An user cannot follow itself.
	all u: User | u->u not in follows
}


pred inv3 {
	// An user only sees (non ad) photos posted by followed users. 
	// Ads can be seen by everyone.
	all u: User, p: Photo, us: User | u->p in sees implies (p in Ad || (us->p in posts implies u->us in follows))
}


pred inv4 {
	// If an user posts an ad then all its posts should be labelled as ads 
	all u: User, a: Ad | u->a in posts implies (all p: Photo | u->p in posts implies p in Ad)
}


pred inv5 {
	// Influencers are followed by everyone else
	all i: Influencer, u: User | i != u implies u->i in follows 
}


pred inv6 {
	// Influencers post every day
	all i: Influencer, d: Day | some p: Photo | i->p in posts && p->d in date
}


pred inv7 {
	// Suggested are other users followed by followers but not yet followed
	all x, y: User | x->y in suggested iff ((some u: User | x->u in follows && u->y in follows) && x!=y && x->y not in follows) 
}


pred inv8 {
	// An user only sees ads from followed or suggested users
	all u: User, a: Ad | u->a in sees implies (some u1: User | u1->a in posts && (u->u1 in follows || u->u1 in suggested))
}

run {}
