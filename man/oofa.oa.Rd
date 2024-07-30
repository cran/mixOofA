\name{oofa.oa}
\alias{oofa.oa}
\title{construct an order-of-addition orthogonal array with m+1 components from an order-of-addition orthogonal array with m components}
\usage{oofa.oa(design)}
\arguments{
\item{design}{an order-of-addition orthogonal array with m components}
}
\value{a component orthogonal array with m+1 components}
\description{
construct an order-of-addition orthogonal array with m+1 components from an order-of-addition orthogonal array with m components
}
\examples{
design <- matrix(c(4,2,3,1,
4,1,3,2,
3,4,2,1,
3,4,1,2,
3,2,1,4,
3,1,2,4,
2,4,3,1,
2,4,1,3,
2,1,3,4,
1,4,3,2,
1,4,2,3,
1,2,3,4), 12, 4, byrow = TRUE)
oofa.oa(design)
}
