\name{D_effi_pwo}
\alias{D_effi_pwo}
\title{D-efficiency from PWO matrix of a given design}
\usage{
D_effi_pwo(X)
}
\arguments{
\item{X}{PWO matrix of a design for order-of-addition experiments}
}
\value{D-efficiency}
\description{Compute D-efficiency from PWO matrix of a given design for order-of-addition experiments}
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
X = PWO(design)
D_effi_pwo(X)
}
