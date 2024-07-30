\name{PWO}
\alias{PWO}
\title{Pair-wise-ordering (PWO) matrix of a given design}
\usage{
PWO(design)
}
\arguments{
\item{design}{a design for order-of-addition experiments}
}
\value{PWO matrix}
\description{Obtain PWO matrix from a given design for order-of-addition experiments}
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
PWO(design)
}
