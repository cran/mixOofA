\name{mixoofa.anova}
\alias{mixoofa.anova}
\title{Anova Table for a mixture order-of-addition experiment}
\usage{mixoofa.anova(formula, response, nmix, mixvar, Zmat, caption)}
\arguments{
\item{formula}{formula for mixture experiment}
\item{response}{response variable}
\item{nmix}{number of mixture components}
\item{mixvar}{matrix representing mixture variables}
\item{Zmat}{matrix containing PWO variables for the components}
\item{caption}{caption for ANOVA table, default is blank}
}
\value{an ANOVA table for mixture order-of-addition experiment}
\description{
obtain ANOVA table for a mixture order-of-addition experiment
}
\examples{
data(fish)
m = 3
mixvar<-fish[, 1:(m+1)]
Zmat<-fish[, (m+2): (m+1+choose(m,2))]
mixoofa.anova(y ~ -1 + (x1+x2+x3)^2, response=fish$y, nmix=m, mixvar, Zmat=Zmat,caption="")
}
